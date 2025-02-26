#![allow(unused)]
use std::fmt;

use crate::parse::*;

pub struct FromFn<F>(F)
where
    F: Fn(&mut fmt::Formatter<'_>) -> fmt::Result;

impl<F> fmt::Debug for FromFn<F>
where
    F: Fn(&mut fmt::Formatter<'_>) -> fmt::Result,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.0)(f)
    }
}

impl<F> fmt::Display for FromFn<F>
where
    F: Fn(&mut fmt::Formatter<'_>) -> fmt::Result,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.0)(f)
    }
}

pub fn immediate(csx: &CotophaData, im: Immediate) -> impl fmt::Display + use<'_> {
    FromFn(move |f| match im {
        Immediate::Integer(i) => write!(f, "{i}"),
        Immediate::Real(r) => write!(f, "{r}"),
        Immediate::String(ix) => write!(f, "{:?}", &csx.strings[ix]),
        Immediate::Nothing(_, ix) => write!(f, "{}", &csx.strings[ix]),
    })
}

pub fn instruction(csx: &CotophaData, i: Instruction) -> impl fmt::Display + use<'_> {
    FromFn(move |f| {
        let CotophaData {
            strings: s, args: a, ..
        } = csx;
        match i {
            Instruction::New { mode, class, name, .. } => {
                write!(f, "New {mode:?} {} {}", &s[class], &s[name])
            }
            Instruction::Free => write!(f, "Free"),
            Instruction::Load { mode, im } => write!(f, "Load {mode:?} {}", immediate(csx, im)),
            Instruction::Store { op } => write!(f, "Store {op:?}"),
            Instruction::Enter { name, args } => write!(f, "Enter {}({})", &s[name], &s[StrIndex(&a[args])]),
            Instruction::Return { free_stack } => write!(f, "Return {free_stack:?}"),
            Instruction::Leave => write!(f, "Leave"),
            Instruction::Element { im } => write!(f, "Element {}", immediate(csx, im)),
            Instruction::ElementIndirect => write!(f, "ElementIndirect"),
            Instruction::Operate { op } => write!(f, "Operate {op:?}"),
            Instruction::UniOperate { uop } => write!(f, "UniOperate {uop:?}"),
            Instruction::Compare { cmp } => write!(f, "Compare {cmp:?}"),
            Instruction::Jump { addr } => write!(f, "Jump {addr}"),
            Instruction::CJump { logic, addr } => write!(f, "Jump{} {addr}", if logic { 'Y' } else { 'N' }),
            Instruction::Call { mode, name, arg_num } => write!(f, "Call {mode:?} {}({arg_num})", &s[name]),
            Instruction::Try { name, catch_addr } => write!(f, "Try {}:{catch_addr}", &s[name]),
            Instruction::Throw { name, arg_num } => write!(f, "Throw {}({arg_num})", &s[name]),
        }
    })
}
