use std::fmt::Write as _;
use std::io::Write as _;

use crate::declare;
use crate::parse::Arg;
use crate::parse::ArrIndex;
use crate::parse::CotophaData;
use crate::parse::Immediate;
use crate::parse::Instruction;
use crate::parse::MCall;
use crate::parse::MCreate;
use crate::parse::MLoad;
use crate::parse::Op;
use crate::parse::Return;
use crate::parse::StrIndex;
use crate::parse::Type;
use crate::parse::Val;
use crate::parse::Var;

struct Stack {
    inner: Vec<SExpr>,
    exprs: Vec<u8>,
    enter: MiniStack,
    clone: Vec<MiniStack>,
}

impl Stack {
    fn split(&mut self) {
        self.clone.push(self.enter);
        let MiniStack { i, e, .. } = self.enter;
        self.enter.i = self.inner.len() as u32;
        self.enter.e = self.exprs.len() as u32;
        self.inner.extend_from_within(i as usize..);
        self.exprs.extend_from_within(e as usize..);
    }

    fn merge(&mut self) -> bool {
        let Some(clone) = self.clone.pop() else {
            return false;
        };
        self.inner.truncate(self.enter.i as usize);
        self.exprs.truncate(self.enter.e as usize);
        self.enter = clone;
        true
    }

    fn enter(&mut self) {
        let items = self.inner.len() - self.enter.i as usize;
        assert!(self.enter.ns < 0 && items < 1 << 16);
        self.enter.ns = (self.enter.ns << 16) | items as i64;
    }

    fn leave(&mut self) {
        let items = self.enter.ns as i16;
        let len = self.enter.i + items as u32;
        assert!(items >= 0);
        self.inner.truncate(len as usize);
        if self.enter.i == len {
            self.exprs.truncate(self.enter.e as usize);
        } else {
            let e = self.inner[self.inner.len() - 1];
            self.exprs.truncate((self.enter.e + e.expr.end) as usize);
        }
        self.enter.ns = (self.enter.ns >> 16) | const { -1 << 48 };
    }

    fn leave_fn(&mut self) {
        self.inner.truncate(self.enter.i as usize);
        self.exprs.truncate(self.enter.e as usize);
        self.enter.ns = -1;
    }

    fn push(&mut self, value: &str) {
        let start = self.exprs.len() as u32 - self.enter.e;
        self.exprs.extend_from_slice(value.as_bytes());
        let expr = ArrIndex(start..start + value.len() as u32);
        self.inner.push(SExpr { expr, prio: Prio::Elt });
    }

    fn push_copy_of(&mut self, n: i32) {
        let n = self.enter.i.wrapping_add_signed(n);
        assert!(self.enter.i <= n && (n as usize) < self.inner.len());
        let SExpr { expr, prio } = self.inner[n as usize];
        let offset = self.exprs.len() as u32 - expr.start - self.enter.e;
        self.exprs
            .extend_from_within((self.enter.e + expr.start) as usize..(self.enter.e + expr.end) as usize);
        let expr = ArrIndex(expr.start + offset..expr.end + offset);
        self.inner.push(SExpr { expr, prio });
    }

    fn push_immediate(&mut self, im: Immediate, csx: &CotophaData) {
        let start = self.exprs.len() as u32 - self.enter.e;
        match im {
            Immediate::Integer(i) => write!(&mut self.exprs, "{i}").unwrap(),
            Immediate::Real(r) => {
                write!(&mut self.exprs, "{r}").unwrap();
                if r.trunc() == r {
                    self.exprs.extend_from_slice(b".0");
                }
            }
            Immediate::String(str) => {
                self.exprs.push(b'"');
                for b in (csx / str).bytes() {
                    match escape_byte(b) {
                        Some(escape) => self.exprs.extend_from_slice(escape.as_bytes()),
                        None => self.exprs.push(b),
                    }
                }
                self.exprs.push(b'"');
            }
            Immediate::Nothing(_, class) => {
                self.exprs.extend_from_slice((csx / class).as_bytes());
            }
        }
        let end = self.exprs.len() as u32 - self.enter.e;
        self.inner.push(SExpr { expr: ArrIndex(start..end), prio: Prio::Im });
    }

    fn push_op(&mut self, op: &str, prio: Prio) {
        assert_ne!(prio, Prio::Call, "use push_call instead");
        if matches!(prio, Prio::Neg | Prio::Not) {
            self.assert_removable(1);
            let e = self.inner.last_mut().unwrap();
            let paren = prio.should_paren(e.prio);
            let extra = 2 * paren as usize + op.len();
            self.exprs.resize(self.exprs.len() + extra, 0);
            let exprs = &mut &mut self.exprs[self.enter.e as usize..];
            write_tail(exprs, if paren { b")" } else { b"" });
            copy_tail(exprs, e.expr);
            write_tail(exprs, if paren { b"(" } else { b"" });
            write_tail(exprs, op.as_bytes());
            e.expr.end += extra as u32;
            e.prio = prio;
        } else if matches!(prio, Prio::Elt) {
            self.assert_removable(1);
            let e = self.inner.last_mut().unwrap();
            self.exprs.reserve(op.len() + 3);
            if prio.should_paren(e.prio) {
                self.exprs.insert((self.enter.e + e.expr.start) as usize, b'(');
                self.exprs.push(b')');
                e.expr.end += 2;
            }
            self.exprs.push(b'.');
            self.exprs.extend_from_slice(op.as_bytes());
            e.expr.end += op.len() as u32 + 1;
            e.prio = prio;
        } else {
            self.assert_removable(2);
            let [a, ref b] = self.inner.last_chunk_mut().unwrap();
            let pa = prio.should_paren(a.prio);
            let pb = prio.should_paren(b.prio);
            let extra = 2 * (pa as usize + pb as usize + 1) + op.len();
            self.exprs.resize(self.exprs.len() + extra, 0);
            let exprs = &mut &mut self.exprs[self.enter.e as usize..];
            write_tail(exprs, if pb { b")" } else { b"" });
            copy_tail(exprs, b.expr);
            write_tail(exprs, if pb { b" (" } else { b" " });
            write_tail(exprs, op.as_bytes());
            write_tail(exprs, if pa { b") " } else { b" " });
            copy_tail(exprs, a.expr);
            write_tail(exprs, if pa { b"(" } else { b"" });
            a.expr.end = b.expr.end + extra as u32;
            a.prio = prio;
            self.inner.pop();
        }
    }

    fn push_indirect(&mut self) {
        self.assert_removable(2);
        let [a, ref b] = self.inner.last_chunk_mut().unwrap();
        let paren = Prio::Elt.should_paren(a.prio);
        let extra = 2 * (1 + paren as usize);
        self.exprs.resize(self.exprs.len() + extra, 0);
        let exprs = &mut &mut self.exprs[self.enter.e as usize..];
        write_tail(exprs, b"]");
        copy_tail(exprs, b.expr);
        write_tail(exprs, if paren { b")[" } else { b"[" });
        copy_tail(exprs, a.expr);
        write_tail(exprs, if paren { b"(" } else { b"" });
        a.expr.end = b.expr.end + extra as u32;
        a.prio = Prio::Elt;
        self.inner.pop();
    }

    fn push_call(&mut self, mode: MCall, name: &str, arg_num: u32) {
        self.assert_removable(arg_num as usize);
        assert_ne!(mode, MCall::Global);
        let this = matches!(mode, MCall::This) as u32;
        assert!(this <= arg_num);
        let paren = this != 0 && Prio::Elt.should_paren(self.inner[self.inner.len() - arg_num as usize].prio);
        let extra = name.len() + 2 * ((arg_num - this).saturating_sub(1) as usize + paren as usize + 1) + this as usize;
        self.exprs.resize(self.exprs.len() + extra, 0);
        let exprs = &mut &mut self.exprs[self.enter.e as usize..];
        let end = exprs.len() as u32;
        write_tail(exprs, b")");
        if arg_num > this {
            copy_tail(exprs, self.inner.pop().unwrap().expr);
            for _ in this..arg_num - 1 {
                write_tail(exprs, b", ");
                copy_tail(exprs, self.inner.pop().unwrap().expr);
            }
        }
        write_tail(exprs, b"(");
        write_tail(exprs, name.as_bytes());
        if this != 0 {
            write_tail(exprs, if paren { b")." } else { b"." });
            copy_tail(exprs, self.inner.pop().unwrap().expr);
            write_tail(exprs, if paren { b"(" } else { b"" });
        }
        let start = exprs.len() as u32;
        self.inner.push(SExpr { expr: ArrIndex(start..end), prio: Prio::Call });
    }

    #[track_caller]
    fn assert_removable(&self, count: usize) {
        let guard = self.enter.guard() as usize;
        assert!(guard + count <= self.inner.len());
    }

    fn top(&self) -> SExpr {
        self.assert_removable(1);
        self.inner[self.inner.len() - 1]
    }

    fn free(&mut self) {
        self.assert_removable(1);
        let s = self.inner.pop().unwrap();
        self.exprs.truncate((self.enter.e + s.expr.start) as usize);
    }

    fn pop(&mut self, strings: &mut String) -> StrIndex {
        self.assert_removable(1);
        let s = self.inner.pop().unwrap();
        let e = self.enter.e as usize;
        let expr = std::str::from_utf8(&self.exprs[e..][s.expr]).unwrap();
        let start = strings.len() as u32;
        strings.push_str(expr);
        let end = strings.len() as u32;
        self.exprs.truncate(e + s.expr.start as usize);
        StrIndex { start, end }
    }

    fn store(&mut self, strings: &mut String, assign: Op) -> Option<(StrIndex, StrIndex)> {
        self.assert_removable(2);
        let [l, ref r] = self.inner.last_chunk_mut().unwrap();
        let e = self.enter.e as usize;
        let lexpr = std::str::from_utf8(&self.exprs[e..][l.expr]).unwrap();
        let rexpr = std::str::from_utf8(&self.exprs[e..][r.expr]).unwrap();
        if matches!(l.prio, Prio::Im) {
            let range = e + l.expr.start as usize..e + l.expr.end as usize;
            match lexpr.as_bytes() {
                b"0" => drop(self.exprs.splice(range, *b"Integer(")),
                b"0.0" => drop(self.exprs.splice(range, *b"Real(")),
                b"\"\"" => drop(self.exprs.splice(range, *b"String(")),
                class => {
                    assert!(
                        class.first().is_some_and(u8::is_ascii_uppercase)
                            && class.iter().all(u8::is_ascii_alphanumeric),
                        "invalid cast: {lexpr}"
                    );
                    self.exprs.insert(range.end, b'(');
                }
            }
            self.exprs.push(b')');
            l.expr.end = (self.exprs.len() - e) as u32;
            l.prio = Prio::Call;
            self.inner.pop();
            return None;
        }
        let ls = strings.len() as u32;
        strings.push_str(lexpr);
        let le = strings.len() as u32;
        strings.push(' ');
        strings.push_str(if assign == Op::Nop { ":=" } else { AOPS[assign as usize] });
        strings.push(' ');
        let rs = strings.len() as u32;
        strings.push_str(rexpr);
        let re = strings.len() as u32;
        self.exprs.truncate(e + l.expr.end as usize);
        self.inner.pop();
        Some((StrIndex { start: ls, end: le }, StrIndex { start: rs, end: re }))
    }
}

fn escape_byte(byte: u8) -> Option<&'static str> {
    let escape = match byte {
        0x7 => "\\a",
        0x8 => "\\b",
        b'\t' => "\\t",
        b'\n' => "\\n",
        0xb => "\\v",
        0xc => "\\f",
        b'\r' => "\\r",
        // b'?' => "\\?",
        b'\\' => "\\\\",
        b'\"' => "\\\"",
        // b'\'' => "\\'",
        _ => return None,
    };
    Some(escape)
}

#[track_caller]
fn write_tail(exprs: &mut &mut [u8], tail: &[u8]) {
    let mid = exprs.len() - tail.len();
    exprs[mid..].copy_from_slice(tail);
    *exprs = &mut std::mem::take(exprs)[..mid];
}

#[track_caller]
fn copy_tail(exprs: &mut &mut [u8], expr: ArrIndex) {
    let mid = exprs.len() - expr.len() as usize;
    exprs.copy_within(expr.start as usize..expr.end as usize, mid);
    *exprs = &mut std::mem::take(exprs)[..mid];
}

#[derive(Debug, Clone, Copy)]
struct MiniStack {
    i: u32,
    e: u32,
    ns: i64,
}

impl MiniStack {
    fn guard(&self) -> u32 {
        self.i + (self.ns as i16).max(0) as u32
    }

    fn depth(&self) -> u8 {
        let [_, a, _, b, _, c, _, d] = self.ns.to_le_bytes();
        4 - (a >> 7) - (b >> 7) - (c >> 7) - (d >> 7)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct SExpr {
    expr: ArrIndex,
    prio: Prio,
}

declare!(enum Prio: u8 { Lor, Land, Cmp, Xor, Or, And, Not, Add, Mul, Neg, Elt, Im, Call });

impl Prio {
    fn should_paren(self, opr: Prio) -> bool {
        match (self, opr) {
            (Prio::Neg, Prio::Not) => false,
            (Prio::Cmp, Prio::Cmp) => true,
            _ => self > opr,
        }
    }
}

fn siupd(sections: &Vec<u32>) -> impl Fn(i32, usize) -> i32 + use<'_> {
    move |si, at| si + sections.get((si + 1) as usize).is_some_and(|&x| x == at as u32) as i32
}

#[non_exhaustive]
pub struct SourceDecompiler<'csx> {
    csx: &'csx CotophaData,
    strings: String,
    nodes: Vec<Node>,
    sections: Vec<u32>,
}

const AOPS: [&str; 10] = ["+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "&&=", "||="];
const OPS: [&str; 10] = ["+", "-", "*", "/", "%", "&", "|", "^", "&&", "||"];
const OPSP: [Prio; 10] = [
    Prio::Add,
    Prio::Add,
    Prio::Mul,
    Prio::Mul,
    Prio::Mul,
    Prio::And,
    Prio::Or,
    Prio::Xor,
    Prio::Land,
    Prio::Lor,
];

const UOPS: [&str; 4] = ["+", "-", "~", "!"];
const UOPSP: [Prio; 4] = [Prio::Neg, Prio::Neg, Prio::Not, Prio::Not];

const CMPS: [&str; 6] = ["!=", "==", "<", "<=", ">", ">="];

impl<'csx> SourceDecompiler<'csx> {
    pub fn new(csx: &'csx CotophaData) -> Self {
        let mut si = -1;
        let mut at = 0;
        let mut pos = Vec::with_capacity(csx.sections.len());
        let mut stack = Stack {
            inner: Vec::with_capacity(4 * 1024),
            exprs: Vec::with_capacity(4 * 1024 * 5),
            enter: MiniStack { i: 0, e: 0, ns: -1 },
            clone: Vec::with_capacity(csx.sections.len()),
        };
        let mut reached = vec![false; csx.image.len()];
        let mut nodes = vec![None; csx.image.len()];
        let mut strings = String::with_capacity(csx.image.len() * 8);
        let mut capacity = 0;
        let siupd = siupd(&csx.sections);

        loop {
            if at >= csx.image.len() || reached[at] {
                if stack.merge() {
                    (at, si) = pos.pop().unwrap();
                    continue;
                }
                break;
            }
            reached[at] = true;

            match csx.image[at] {
                Instruction::New { mode, class, name, .. } => {
                    if matches!(mode, MCreate::Stack) {
                        stack.push(csx / name);
                    }
                    nodes[at] = Some(Node::New { mode, class, name });
                }
                Instruction::Free if stack.top().prio == Prio::Call => {
                    let expr = stack.pop(&mut strings);
                    nodes[at] = Some(Node::Call { expr });
                }
                Instruction::Free => stack.free(),
                Instruction::Load { mode, im } => match mode {
                    MLoad::Immediate => stack.push_immediate(im, csx),
                    MLoad::Stack => match im {
                        Immediate::Integer(n) => stack.push_copy_of(n),
                        Immediate::String(name) => stack.push(csx / name),
                        _ => panic!("object does not exist on the stack"),
                    },
                    MLoad::This => match im {
                        Immediate::String(name) => {
                            stack.push("this");
                            stack.push_op(csx / name, Prio::Elt);
                        }
                        Immediate::Nothing(Type::Reference, _) => stack.push("this"),
                        _ => panic!("member object does not exist"),
                    },
                    MLoad::Global => match im {
                        Immediate::Integer(i) if 0 <= i && (i as u32) < csx.global_num => {
                            let name = (*csx.global)[i as usize].name;
                            stack.push("global");
                            if name.is_empty() {
                                stack.push_immediate(im, csx);
                                stack.push_indirect();
                            } else {
                                stack.push_op(csx / name, Prio::Elt);
                            }
                        }
                        _ => panic!("global object does not exist"),
                    },
                    MLoad::Data => match im {
                        Immediate::Integer(i) if 0 <= i && (i as u32) < csx.data_num => {
                            let name = (*csx.data)[i as usize].name;
                            stack.push("static");
                            if name.is_empty() {
                                stack.push_immediate(im, csx);
                                stack.push_indirect();
                            } else {
                                stack.push_op(csx / name, Prio::Elt);
                            }
                        }
                        _ => panic!("data object does not exist"),
                    },
                },
                Instruction::Store { op: assign } => {
                    if let Some((place, value)) = stack.store(&mut strings, assign) {
                        nodes[at] = Some(Node::Assignment { place, assign, value });
                    }
                }
                Instruction::Enter { name, mut args } => {
                    let vars = csx / args;
                    if matches!(vars, &[Arg { ty: Type::Reference, name, .. }, ..] if csx / name == "this") {
                        assert!((csx / name).contains("::"));
                        args.start += 1;
                    }
                    let args = StrIndex(csx / args);

                    if name.is_empty() {
                        let depth = stack.enter.depth();
                        nodes[at] = Some(Node::Begin { depth });
                    } else if csx / name == "@CATCH" {
                        nodes[at] = Some(Node::Catch { args });
                    } else {
                        stack.leave_fn();
                        nodes[at] = Some(Node::Function { name, args });
                        capacity += 1;
                    }

                    for &Arg { name, .. } in vars {
                        stack.push(csx / name);
                    }
                    stack.enter();
                }
                Instruction::Return { free_stack } => {
                    assert!(free_stack != Return::TailCall, "tail call returns aren't supported");
                    let has_value = matches!(free_stack, Return::Normal);
                    let value = match has_value {
                        true => stack.pop(&mut strings),
                        false => <_>::default(),
                    };
                    nodes[at] = Some(Node::Return { has_value, value });
                }
                Instruction::Leave => {
                    stack.leave();
                    let depth = stack.enter.depth();
                    nodes[at] = Some(Node::End { depth });
                }
                Instruction::Element { im } => {
                    let Immediate::String(ident) = im else {
                        panic!("immediate is not a field");
                    };
                    stack.push_op(csx / ident, Prio::Elt);
                }
                Instruction::ElementIndirect => stack.push_indirect(),
                Instruction::Operate { op: Op::Nop } => panic!("unexpected nop in Operate"),
                Instruction::Operate { op } => stack.push_op(OPS[op as usize], OPSP[op as usize]),
                Instruction::UniOperate { uop } => stack.push_op(UOPS[uop as usize], UOPSP[uop as usize]),
                Instruction::Compare { cmp } => stack.push_op(CMPS[cmp as usize], Prio::Cmp),
                Instruction::Jump { addr } => nodes[at] = Some(Node::Branch { ctrl: Ctrl::Undef, addr }),
                Instruction::CJump { logic, addr } => {
                    assert!(!logic, "can't handle positive logic");
                    let cond = stack.pop(&mut strings);
                    nodes[at] = Some(Node::BranchN { ctrl: CtrlC::Undef, addr, cond });
                }
                Instruction::Call { mode, name, arg_num } => stack.push_call(mode, csx / name, arg_num),
                Instruction::Try { name, catch_addr } => {
                    assert_eq!(csx / name, "@TRY");
                    stack.enter();
                    nodes[at] = Some(Node::Try { catch_addr });
                }
                Instruction::Throw { name, arg_num } => {
                    assert_eq!(csx / name, "@CATCH");
                    stack.push_call(MCall::Auto, "Throw", arg_num);
                    let expr = stack.pop(&mut strings);
                    nodes[at] = Some(Node::Call { expr });
                }
            }

            capacity += nodes[at].is_some() as usize;
            if let Some(Branch { addr, .. } | BranchN { addr, .. } | Try { catch_addr: addr }) = nodes[at] {
                if !matches!(nodes[at], Some(Branch { .. })) {
                    stack.split();
                    pos.push((at + 1, siupd(si, at + 1)));
                }
                si += addr;
                at = csx.sections[si as usize] as usize;
            } else {
                at += 1;
                si = siupd(si, at);
            }
        }

        for at in 0..csx.image.len() {
            if reached[at] {
                continue;
            }

            match csx.image[at] {
                Instruction::Leave => (),
                Instruction::Jump { addr } => nodes[at] = Some(Node::Branch { ctrl: Ctrl::Undef, addr }),
                other => unreachable!("unreachable code: {other:?}"),
            }
        }

        let mut compact = Vec::with_capacity(capacity);
        let mut sections = Vec::with_capacity(csx.sections.len());
        let mut si = -1;
        let mut last_upd = 0;
        for (at, opt) in nodes.into_iter().enumerate() {
            let new_si = siupd(si, at);
            if new_si > si && last_upd < compact.len() {
                last_upd = compact.len();
                sections.push(last_upd as u32);
            }
            si = new_si;

            if let Some(Node::Assignment { mut place, assign: Op::Nop, value }) = opt
                && last_upd < compact.len()
                && let Some(last) = compact.last_mut()
                && let Node::New { mode, class, name } = *last
                && let prefix = match mode {
                    MCreate::Stack => "",
                    MCreate::This => "this.",
                }
                && let Some(ident) = strings[place].strip_prefix(prefix)
                && csx / name == ident
            {
                place.start += prefix.len() as u32;
                *last = Node::AssignedNew { mode, class, name: place, value };
            } else if let Some(Node::Branch { ctrl, addr: addr @ ..0 }) = opt
                && let Node::ForNext { .. } = compact[sections[(si + addr) as usize] as usize]
            {
                assert_eq!(ctrl, Ctrl::Undef);
                compact.push(Node::Branch { ctrl: Ctrl::Next, addr });
            } else if let Some(node) = opt {
                if matches!(node, Node::Function { .. }) && compact.len() > 0 {
                    compact.push(Node::EndFunc);
                }
                compact.push(node);
            }

            #[rustfmt::skip]
            if let Some(&[
                Begin { depth: da },
                AssignedNew { mode: MCreate::Stack, class, name, value: init },
                Branch { addr: 2, .. },
                Assignment { place, assign, value: step },
                BranchN { addr: 1, cond, .. },
                End { depth: db },
                Branch { addr, .. },
            ]) = compact.last_chunk() {
                assert!(addr > 0);
                assert_eq!(last_upd, compact.len() - 3);
                assert_eq!(sections.iter().nth_back(1), Some(&(last_upd as u32 - 1)));
                assert_eq!(da, db);
                assert_eq!(csx / class, "Integer");
                assert_eq!(&strings[name], &strings[place]);
                assert!(strings[cond].strip_prefix(&strings[name]).is_some_and(|x| x.starts_with(" > ")));
                assert_eq!(assign, Op::Add);
                assert_eq!(&strings[step], "1");

                compact.truncate(compact.len() - 7);
                sections.truncate(sections.len() - 2);
                compact.push(ForInit { class, name, value: init });
                compact.push(ForTest { cond });
                sections.push(compact.len() as u32);
                compact.push(ForNext { place, assign, value: step });
                sections.push(compact.len() as u32);
                compact.push(ForExit { addr });
                last_upd = compact.len() - 1;
            };
        }

        if compact.len() > 0 {
            compact.push(Node::EndFunc);
        }

        assert!(sections.windows(2).all(|w| w[0] < w[1]));

        Self { csx, strings, nodes: compact, sections }
    }
}

#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
enum Node {
    New { mode: MCreate, class: StrIndex, name: StrIndex },
    AssignedNew { mode: MCreate, class: StrIndex, name: StrIndex, value: StrIndex },
    Assignment { place: StrIndex, assign: Op, value: StrIndex },
    Return { has_value: bool, value: StrIndex },
    Call { expr: StrIndex },
    Function { name: StrIndex, args: StrIndex },
    EndFunc,
    Structure { name: StrIndex },
    EndStruct,
    Begin { depth: u8 },
    PrivateLabel { l: u32 },
    End { depth: u8 },
    Try { catch_addr: i32 },
    Catch { args: StrIndex },
    EndTry,
    Branch { ctrl: Ctrl, addr: i32 },
    BranchN { ctrl: CtrlC, addr: i32, cond: StrIndex },
    ForInit { class: StrIndex, name: StrIndex, value: StrIndex },
    ForTest { cond: StrIndex },
    ForNext { place: StrIndex, assign: Op, value: StrIndex },
    ForExit { addr: i32 },
    Repeat,
    Else,
    EndIf,
}

use Node::*;

declare!(enum Ctrl: u8 { Undef, Break, Continue, EndWhile, Next, Goto, Mute });
declare!(enum CtrlC: u8 { Undef, While, Until, If, ElseIf });
declare!(enum ScopeOpener: u8 { Function, Structure, Begin, Try, If, Else, While, Repeat, For });

pub struct Source<'csx> {
    csx: &'csx CotophaData,
    strings: String,
    nodes: Vec<Node>,
}

impl<'csx> Source<'csx> {
    pub fn new(sd: SourceDecompiler<'csx>) -> Self {
        let SourceDecompiler { csx, strings, mut nodes, sections } = sd;
        let mut si = sections.len() as i32 - 1;
        for at in (0..nodes.len()).rev() {
            if let Branch { ctrl: Ctrl::Undef, addr } = nodes[at] {
                let target = sections[(si + addr) as usize] as usize;
                if addr <= 0 {
                    let BranchN { ctrl, addr: brk, cond } = nodes[target] else {
                        panic!("missing while branch at {target}");
                    };
                    assert_eq!(brk + addr, 1);
                    assert_eq!(sections[(si + 1) as usize] as usize, at + 1);
                    match ctrl {
                        CtrlC::Undef => {
                            nodes[at] = Branch { ctrl: Ctrl::EndWhile, addr };
                            nodes[target] = BranchN { ctrl: CtrlC::While, addr: brk, cond };
                        }
                        CtrlC::While => nodes[at] = Branch { ctrl: Ctrl::Continue, addr },
                        _ => panic!("unrecognized control: expected While, got {ctrl:?}"),
                    }
                } else if let Branch { ctrl: Ctrl::EndWhile, addr: c, .. }
                | BranchN { ctrl: CtrlC::Until, addr: c, .. } = nodes[target - 1]
                {
                    if addr <= 1 - c {
                        nodes[at] = Branch { ctrl: Ctrl::Break, addr };
                    }
                }
            } else if let BranchN { ctrl: CtrlC::Undef, addr, cond } = nodes[at] {
                let target = sections[(si + addr) as usize] as usize;
                if addr <= 0 {
                    if let Begin { depth: da } = nodes[target]
                        && let End { depth: db } = nodes[at - 1]
                        && da == db
                    {
                        nodes[target] = Repeat;
                        nodes[at] = BranchN { ctrl: CtrlC::Until, addr, cond };
                    } else {
                        panic!("no Begin..End surrounding repeat loop");
                    }
                }
            }
            si -= sections.get(si as usize).is_some_and(|&x| x == at as u32) as i32;
        }

        let siupd = siupd(&sections);
        si = -1;
        for at in 0..nodes.len() {
            si = siupd(si, at);
            if let End { depth: 0 } = nodes[at]
                && let Branch { ctrl: Ctrl::Undef, addr } = nodes[at + 1]
                && let target = sections[(si + addr) as usize] as usize
                && let Begin { depth: 0 | 1 } = nodes[target]
            {
                nodes[at + 1] = Branch { ctrl: Ctrl::Goto, addr };
                nodes[target] = PrivateLabel { l: 0 };
            } else if let Try { catch_addr } = nodes[at]
                && let brk_try = sections[(si + catch_addr) as usize] as usize - 1
                && let Branch { ctrl: Ctrl::Undef, addr } = nodes[brk_try]
                && let end_try = sections[(si + addr) as usize] as usize
                && let End { .. } = nodes[end_try]
            {
                nodes[brk_try] = Branch { ctrl: Ctrl::Mute, addr };
                nodes[end_try] = EndTry;
            }
        }

        const ELSE: u32 = 1 << 31;
        let mut endifs = vec![0; sections.len()];
        let mut else_ends = vec![-1; sections.len()];
        si = -1;
        for at in 0..nodes.len() {
            let upd = siupd(si, at) - si;
            si += upd;
            let BranchN { ctrl: CtrlC::Undef, addr, cond } = nodes[at] else {
                continue;
            };
            nodes[at] = BranchN { ctrl: CtrlC::If, addr, cond };

            let nii = sections[(si + addr) as usize] as usize;
            let end = if let Branch { ctrl: Ctrl::Undef, addr: endif } = nodes[nii - 1] {
                nodes[nii - 1] = Branch { ctrl: Ctrl::Mute, addr: endif };
                if endif != 1 {
                    assert_eq!(endifs[(si + addr) as usize], 0);
                    endifs[(si + addr) as usize] = ELSE;
                    else_ends[(si + addr) as usize] = si + addr + endif - 1;
                }
                si + addr + endif - 1
            } else {
                si + addr
            };

            if upd != 0 && else_ends[si as usize] == end {
                assert_eq!(endifs[si as usize], ELSE);
                endifs[si as usize] = 0;
                nodes[at] = BranchN { ctrl: CtrlC::ElseIf, addr, cond };
            } else {
                endifs[end as usize] += 1;
            }
        }
        drop(else_ends);

        let mut kind = 0;
        for at in 0..nodes.len() {
            if let Function { mut name, .. } = nodes[at]
                && let fn_name = csx / name
                && let mid @ 2.. = fn_name.len() / 2
                && let Some("::") = fn_name.get(mid - 1..mid + 1)
                && fn_name[..mid - 1] == fn_name[mid + 1..]
            {
                assert_eq!(kind, 0);
                name.start += (mid + 1) as u32;
                nodes[at] = Structure { name };
                kind = 2;
            } else if let Function { .. } = nodes[at] {
                assert_eq!(kind, 0);
                kind = 1;
            } else if let EndFunc = nodes[at] {
                match kind {
                    1 => (),
                    2 => nodes[at] = EndStruct,
                    _ => panic!("unknown named scope kind"),
                }
                kind = 0;
            }
        }

        let mut l = 0;
        for at in 0..nodes.len() {
            match nodes[at] {
                EndFunc => l = 0,
                PrivateLabel { .. } => {
                    l += 1;
                    nodes[at] = PrivateLabel { l };
                }
                _ => continue,
            }
        }

        si = -1;
        for at in 0..nodes.len() {
            si = siupd(si, at);
            if let Branch { ctrl: Ctrl::Goto, addr } = nodes[at] {
                let target = sections[(si + addr) as usize] as usize;
                let PrivateLabel { l } = nodes[target] else {
                    panic!("Goto does not point to Label");
                };
                nodes[at] = Branch { ctrl: Ctrl::Goto, addr: l as i32 };
            }
        }

        let mut sco = Vec::with_capacity(0);
        let mut compact = Vec::with_capacity(nodes.len());
        si = -1;
        for at in 0..nodes.len() {
            let upd = siupd(si, at) - si;
            si += upd;
            if upd != 0 {
                if endifs[si as usize] == ELSE {
                    assert_eq!(sco.pop(), Some(ScopeOpener::If));
                    sco.push(ScopeOpener::Else);
                    compact.push(Else);
                }
                for _ in 0..endifs[si as usize] & !ELSE {
                    assert!(matches!(sco.pop(), Some(ScopeOpener::If | ScopeOpener::Else)));
                    compact.push(EndIf);
                }
            }
            match nodes[at] {
                Node::Return { .. } if matches!(nodes[at + 1], EndFunc | EndStruct) => continue,
                Function { .. } => sco.push(ScopeOpener::Function),
                EndFunc => assert_eq!(sco.pop(), Some(ScopeOpener::Function)),
                Structure { .. } => sco.push(ScopeOpener::Structure),
                EndStruct => assert_eq!(sco.pop(), Some(ScopeOpener::Structure)),
                Begin { .. } if !matches!(nodes[at - 1], ForExit { .. }) => sco.push(ScopeOpener::Begin),
                End { .. } if sco.last() == Some(&ScopeOpener::Begin) => drop(sco.pop()),
                End { .. } => continue,
                Try { .. } => sco.push(ScopeOpener::Try),
                Catch { .. } => assert_eq!(sco.last(), Some(&ScopeOpener::Try)),
                EndTry => assert_eq!(sco.pop(), Some(ScopeOpener::Try)),
                Branch { ctrl, .. } => match ctrl {
                    Ctrl::Undef => panic!("unconditional branch undefined"),
                    Ctrl::EndWhile => assert_eq!(sco.pop(), Some(ScopeOpener::While)),
                    Ctrl::Next => assert_eq!(sco.pop(), Some(ScopeOpener::For)),
                    Ctrl::Break | Ctrl::Continue | Ctrl::Goto => (),
                    Ctrl::Mute => continue,
                },
                BranchN { ctrl, .. } => match ctrl {
                    CtrlC::Undef => panic!("conditional branch undefined"),
                    CtrlC::While => sco.push(ScopeOpener::While),
                    CtrlC::Until => assert_eq!(sco.pop(), Some(ScopeOpener::Repeat)),
                    CtrlC::If => sco.push(ScopeOpener::If),
                    CtrlC::ElseIf => assert_eq!(sco.last(), Some(&ScopeOpener::If)),
                },
                ForExit { .. } => sco.push(ScopeOpener::For),
                Repeat => sco.push(ScopeOpener::Repeat),
                Else | EndIf => unreachable!(),
                _ => (),
            }
            compact.push(nodes[at]);
        }

        nodes = compact;
        Self { csx, strings, nodes }
    }

    pub fn to_contents(&self) -> (String, Vec<StrIndex>) {
        let mut s = String::with_capacity(self.csx.image.len() * 16);
        let mut ixs = Vec::with_capacity(self.csx.function.entries.len() / 2);
        let &Self { csx, ref strings, ref nodes } = self;
        s += "Include \"cotopha.ch\"\n";
        s += r#"@IF @IsDefined("__DEFINITIONS_CH__") == 0"#;
        s += "\n\nConstant __DEFINITIONS_CH__ := -1\n\n";
        for &node in nodes {
            let Structure { name } = node else {
                continue;
            };
            writeln!(s, "DeclareType {}", csx / name).unwrap();
        }
        s += "\n";
        for &Var { name, .. } in &csx.global[ArrIndex(..csx.global_num)] {
            writeln!(s, "DeclareDef {}", csx / name).unwrap();
        }
        s += "\n";
        for &Var { name, .. } in &csx.data[ArrIndex(..csx.data_num)] {
            writeln!(s, "DeclareDef Data {}", csx / name).unwrap();
        }
        s += "\n@ENDIF\n";
        s += "\n";

        let start = s.len() as u32;
        ixs.push(StrIndex { start: 0, end: start });

        #[track_caller]
        fn write_non_default_value(s: &mut String, csx: &CotophaData, value: Val) {
            match value {
                Val::Array(..) => todo!("global array initializers are not yet supported"),
                Val::Integer(i) => write!(s, "{i}").unwrap(),
                Val::Real(r) => {
                    write!(s, "{r}").unwrap();
                    if r.trunc() == r {
                        *s += ".0";
                    }
                }
                Val::String { ix } => {
                    *s += "\"";
                    for ch in (csx / ix).chars() {
                        match escape_byte(ch as u8) {
                            Some(escape) if ch.is_ascii() => *s += escape,
                            _ => s.push(ch),
                        }
                    }
                    *s += "\"";
                }
                Val::Other { sp } => unreachable!("{} can't have non-default value", csx / sp),
            }
        }

        s += "Include \"definitions.ch\"\n\n";

        for &Var { name, value } in &csx.global[ArrIndex(..csx.global_num)] {
            assert!(!name.is_empty());
            let name = csx / name;
            let class = csx / value.class();
            if value.is_default() {
                writeln!(s, "{class} {name}").unwrap();
                continue;
            }

            write!(s, "{class} {name} := ").unwrap();
            match value {
                Val::Array(..) => todo!("global array initializers are not yet supported"),
                _ => write_non_default_value(&mut s, csx, value),
            }
            s += "\n";
        }
        s += "\n";

        for &Var { name, value } in &csx.data[ArrIndex(..csx.data_num)] {
            assert!(!name.is_empty());
            let name = csx / name;
            let class = csx / value.class();
            if value.is_default() {
                writeln!(s, "Data {name} : {class}").unwrap();
                continue;
            }

            let Val::Array(aix) = value else {
                panic!("Data section must contain default value, or array of constants")
            };

            write!(s, "Data {name}\n\t").unwrap();
            for &Var { name, value } in &csx.data[aix] {
                if !name.is_empty() {
                    write!(s, "{} := ", csx / name).unwrap();
                } else {
                    s += ":= ";
                }
                write_non_default_value(&mut s, csx, value);
                s += ", ";
            }
            s.replace_range(s.len() - 2.., "\nEndData\n");
        }
        s += "\n";

        let end = s.len() as u32;
        ixs.push(StrIndex { start, end });

        let combine = |StrIndex { start, .. }, StrIndex { end, .. }| &strings[StrIndex { start, end }];
        let mut tabs = 0;
        let mut nlen = 0;
        let mut init = false;
        let mut start = end;
        for (at, &node) in nodes.iter().enumerate() {
            if s.len() == start as usize {
                s += "Include \"definitions.ch\"\n\n";
            }
            if s.ends_with("\n") {
                if let EndFunc
                | EndStruct
                | PrivateLabel { .. }
                | End { .. }
                | Catch { .. }
                | EndTry
                | Else
                | EndIf
                | Branch { ctrl: Ctrl::EndWhile | Ctrl::Next, .. }
                | BranchN { ctrl: CtrlC::Until | CtrlC::ElseIf, .. } = node
                {
                    tabs -= 1;
                }
                assert!(tabs >= 0 || tabs == -1 && init && matches!(node, EndFunc));
                (0..tabs).for_each(|_| s.push_str("\t"));
            }
            match node {
                New { class, name, .. } => writeln!(s, "{} {}", csx / class, csx / name).unwrap(),
                AssignedNew { class, name, value, .. } => {
                    writeln!(s, "{} {}", csx / class, combine(name, value)).unwrap()
                }
                Assignment { place, value, .. } => writeln!(s, "{}", combine(place, value)).unwrap(),
                Node::Return { has_value: false, .. } => s += "Return\n",
                Node::Return { value, .. } => writeln!(s, "Return {}", &strings[value]).unwrap(),
                Call { expr } => s = s + &strings[expr] + "\n",
                Function { name, .. } if csx / name == "@Initialize" => (tabs, init) = (tabs - 1, true),
                Function { name, args } => writeln!(s, "Function {}({})", csx / name, csx / args).unwrap(),
                EndFunc if init => {
                    let end = s.len() as u32;
                    ixs.push(StrIndex { start, end });
                    (tabs, init, start) = (tabs + 1, false, end);
                }
                EndFunc => s += "EndFunc\n\n",
                Structure { name } => writeln!(s, "Structure {}", csx / name).unwrap(),
                EndStruct => s += "EndStruct\n\n",
                Begin { .. } if matches!(nodes[at - 1], ForExit { .. }) => continue,
                Begin { .. } => s += "Begin\n",
                PrivateLabel { l } => writeln!(s, "Label L{l}").unwrap(),
                End { .. } => s += "End\n",
                Try { .. } => s += "Try\n",
                Catch { args } => writeln!(s, "Catch({})", csx / args).unwrap(),
                EndTry => s += "EndTry\n",
                Branch { ctrl, addr } => match ctrl {
                    Ctrl::Break => s += "Break\n",
                    Ctrl::Continue => s += "Continue\n",
                    Ctrl::EndWhile => s += "EndWhile\n",
                    Ctrl::Next => s += "Next\n",
                    Ctrl::Goto => writeln!(s, "Goto L{addr}").unwrap(),
                    Ctrl::Undef | Ctrl::Mute => unreachable!(),
                },
                BranchN { ctrl, cond, .. } => match ctrl {
                    CtrlC::While => writeln!(s, "While {}", &strings[cond]),
                    CtrlC::Until => writeln!(s, "Until {}", &strings[cond]),
                    CtrlC::If => writeln!(s, "If {}", &strings[cond]),
                    CtrlC::ElseIf => writeln!(s, "ElseIf {}", &strings[cond]),
                    CtrlC::Undef => unreachable!(),
                }
                .unwrap(),
                ForInit { name, value, .. } => {
                    nlen = (name.end - name.start) as usize + 3;
                    write!(s, "For {}", combine(name, value)).unwrap();
                }
                ForTest { cond } => write!(s, " To {}", &strings[cond][nlen..]).unwrap(),
                ForNext { .. } => (),
                ForExit { .. } => s += "\n",
                Repeat => s += "Repeat\n",
                Else => s += "Else\n",
                EndIf => s += "EndIf\n",
            }
            if let Function { .. }
            | Structure { .. }
            | Begin { .. }
            | PrivateLabel { .. }
            | Try { .. }
            | Catch { .. }
            | ForExit { .. }
            | Repeat
            | Else
            | BranchN { ctrl: CtrlC::While | CtrlC::If | CtrlC::ElseIf, .. } = node
            {
                tabs += 1;
            }
        }
        assert_eq!(tabs, 0);
        (s, ixs)
    }
}
