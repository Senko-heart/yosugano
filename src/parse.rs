use std::fmt;
use std::io;
use std::io::Read;
use std::ops::Div;
use std::ops::Index;
use std::ops::Range;
use std::ops::RangeTo;

use crate::declare;
use crate::ioex::exhaust;
use crate::ioex::BinaryData;
use crate::ioex::Len;
use crate::ioex::ReadEx;
use crate::ioex::TryFromBytes;

declare!(struct Entis = b"Entis\x1a\0\0");
declare!(enum FileId: i32 { Undefined = -1 });
declare!(enum Reserved: u32 { Zero });
declare!(struct CotophaImageFile = b"Cotopha Image file\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0");

#[non_exhaustive]
#[derive(Debug)]
pub struct Header {
    pub length: u32,
}

impl BinaryData for Header {
    fn read(source: &mut impl io::Read) -> io::Result<Self> {
        Entis = source.read_value()?;
        FileId::Undefined = source.read_value()?;
        Reserved::Zero = source.read_value()?;
        CotophaImageFile = source.read_value()?;
        let length = source.read_value()?;
        Reserved::Zero = source.read_value()?;
        Ok(Self { length })
    }
}

#[non_exhaustive]
#[derive(Debug)]
pub struct SectionHeader {
    pub name: ByteStr<8>,
    pub length: u32,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ByteStr<const N: usize>(pub [u8; N]);

impl<const N: usize> fmt::Debug for ByteStr<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!(r#"b"{}""#, self.0.escape_ascii()))
    }
}

impl BinaryData for SectionHeader {
    fn read(source: &mut impl io::Read) -> io::Result<Self> {
        let name = ByteStr(source.read_value()?);
        let length = source.read_value()?;
        Reserved::Zero = source.read_value()?;
        Ok(Self { name, length })
    }
}

pub struct CotophaData {
    pub image: Vec<Instruction>,
    pub sections: Vec<u32>,
    pub function: Function,
    pub global: Box<[Var]>,
    pub global_num: u32,
    pub data: Box<[Var]>,
    pub data_num: u32,
    pub strings: String,
    pub args: Vec<Arg>,
    pub conststr: Box<[StrIndex]>,
}

impl<'a> Div<StrIndex> for &'a CotophaData {
    type Output = &'a str;

    fn div(self, rhs: StrIndex) -> Self::Output {
        &self.strings[rhs]
    }
}

impl<'a> Div<ArrIndex> for &'a CotophaData {
    type Output = &'a [Arg];

    fn div(self, rhs: ArrIndex) -> Self::Output {
        &self.args[rhs]
    }
}

const STRINGS: &str = "ReferenceArrayHashIntegerRealString";

impl BinaryData for CotophaData {
    fn read(source: &mut impl io::Read) -> io::Result<Self> {
        let header: Header = source.read_data()?;
        let source = &mut source.take(header.length as _);
        let mut ret = Self {
            image: vec![],
            sections: vec![],
            function: Function::default(),
            global: Box::default(),
            global_num: 0,
            data: Box::default(),
            data_num: 0,
            strings: STRINGS.into(),
            args: Vec::with_capacity(1024),
            conststr: Box::default(),
        };
        while source.limit() > 0 {
            let sh: SectionHeader = source.read_data()?;
            let limit = source.limit().saturating_sub(sh.length as _);
            let ctx = &mut ret;
            source.set_limit(sh.length as _);
            match &sh.name.0 {
                b"image   " => Image { this: ctx.image, sections: ctx.sections } = Image::read(source, ctx)?,
                b"function" => ctx.function = Function::read(source, ctx)?,
                b"global  " => Storage { this: ctx.global, num: ctx.global_num } = <Storage<true>>::read(source, ctx)?,
                b"data    " => Storage { this: ctx.data, num: ctx.data_num } = <Storage<false>>::read(source, ctx)?,
                b"conststr" => ConstStr { conststr: ctx.conststr } = ConstStr::read(source, ctx)?,
                b"linkinf " => LinkInf {} = LinkInf::read(source, ctx)?,
                _ => (),
            }
            exhaust(source)?;
            source.set_limit(limit);
        }

        if !ret.conststr.is_empty() {
            let put_conststr = |ix: &mut StrIndex| {
                if (ix.start as i32) < 0 {
                    let Some(&cix) = ret.conststr.get(ix.end as usize) else {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            format!(
                                "conststr index out of bounds: the len is {} but the index is {}",
                                ret.conststr.len(),
                                ix.end
                            ),
                        ));
                    };
                    *ix = cix;
                }
                Ok(())
            };

            let mut argbuf = String::new();
            for i in &mut ret.image {
                match i {
                    Instruction::New { class, name, .. } => {
                        put_conststr(class)?;
                        put_conststr(name)?;
                    }
                    Instruction::Load { im: Immediate::String(ix), .. } => put_conststr(ix)?,
                    Instruction::Load { im: Immediate::Nothing(Type::Object, sp), .. } => put_conststr(sp)?,
                    Instruction::Enter { name, args } => {
                        put_conststr(name)?;
                        if ret.args[*args]
                            .iter()
                            .any(|arg| arg.class.is_empty() || arg.name.is_empty())
                        {
                            argbuf.clear();
                            argbuf.reserve(128);
                            let len = ret.strings.len() as u32;
                            for arg in args.start..args.end {
                                let Arg { class, name, .. } = &mut ret.args[arg as usize];
                                put_conststr(class)?;
                                put_conststr(name)?;

                                if arg != args.start {
                                    argbuf.push_str(", ");
                                }

                                let start = len + argbuf.len() as u32;
                                argbuf.push_str(&ret.strings[*class]);
                                let end = len + argbuf.len() as u32;
                                *class = StrIndex { start, end };

                                argbuf.push_str(" ");

                                let start = len + argbuf.len() as u32;
                                argbuf.push_str(&ret.strings[*name]);
                                let end = len + argbuf.len() as u32;
                                *name = StrIndex { start, end };
                            }
                            ret.strings.push_str(&argbuf);
                        }
                    }
                    Instruction::Element { im: Immediate::String(ix) } => put_conststr(ix)?,
                    Instruction::Element { im: Immediate::Nothing(Type::Object, sp), .. } => put_conststr(sp)?,
                    Instruction::Call { name, .. } => put_conststr(name)?,
                    Instruction::Try { name, .. } => put_conststr(name)?,
                    Instruction::Throw { name, .. } => put_conststr(name)?,
                    _ => (),
                }
            }
        }

        Ok(ret)
    }
}

#[derive(Debug, Clone, Default)]
pub struct Image {
    pub this: Vec<Instruction>,
    pub sections: Vec<u32>,
}

impl Image {
    pub fn read(source: &mut io::Take<&mut impl io::Read>, ctx: &mut CotophaData) -> io::Result<Self> {
        let mut this = Vec::with_capacity(source.limit() as usize * 2 / 19);
        let mut bytepos = Vec::with_capacity(this.capacity());
        let mut sections = Vec::with_capacity(source.limit() as usize / 110);
        let mut branches = Vec::with_capacity(sections.capacity());
        ctx.strings.reserve(source.limit() as usize * 4 / 11);
        let limit = source.limit() as u32;
        while let Some(ic) = source.try_read_value()? {
            bytepos.push(limit - source.limit() as u32 - 1);
            let i = match ic {
                InstructionCode::New => {
                    let mode = source.read_value()?;
                    let ty = source.read_value()?;
                    let class = read_class(source, ctx, ty)?;
                    let name = StrIndex::read(source, ctx)?;
                    Instruction::New { mode, ty, class, name }
                }
                InstructionCode::Free => Instruction::Free,
                InstructionCode::Load => Instruction::Load {
                    mode: source.read_value()?,
                    im: Immediate::read(source, ctx)?,
                },
                InstructionCode::Store => Instruction::Store { op: source.read_value()? },
                InstructionCode::Enter => {
                    let name = StrIndex::read(source, ctx)?;
                    let len: i32 = source.read_value()?;
                    if len == -1 {
                        TypeCode::Zero = source.read_value()?;
                        let catch_addr = source.read_value()?;
                        Instruction::Try { name, catch_addr }
                    } else {
                        let args = ArrIndex::read_args(&mut len.to_le_bytes().chain(&mut *source), ctx)?;
                        Instruction::Enter { name, args }
                    }
                }
                InstructionCode::Leave => Instruction::Leave,
                InstructionCode::Jump => Instruction::Jump { addr: source.read_value()? },
                InstructionCode::CJump => {
                    Instruction::CJump { logic: source.read_value()?, addr: source.read_value()? }
                }
                InstructionCode::Call => {
                    let mode = source.read_value()?;
                    let arg_num = source.read_value()?;
                    let name = StrIndex::read(source, ctx)?;
                    if matches!(mode, Mode::Immediate) {
                        Throw::Valid = source.read_value()?;
                        Instruction::Throw { arg_num, name }
                    } else {
                        let mode = MCall::try_from_le_bytes([mode as u8])?;
                        Instruction::Call { mode, arg_num, name }
                    }
                }
                InstructionCode::Return => Instruction::Return { free_stack: source.read_value()? },
                InstructionCode::Element => Instruction::Element { im: Immediate::read(source, ctx)? },
                InstructionCode::ElementIndirect => Instruction::ElementIndirect,
                InstructionCode::Operate => Instruction::Operate { op: source.read_value()? },
                InstructionCode::UniOperate => Instruction::UniOperate { uop: source.read_value()? },
                InstructionCode::Compare => Instruction::Compare { cmp: source.read_value()? },
            };
            if let Instruction::Jump { addr }
            | Instruction::CJump { addr, .. }
            | Instruction::Try { catch_addr: addr, .. } = i
            {
                let src = limit - source.limit() as u32;
                let dest = src.wrapping_add_signed(addr);
                if dest > limit {
                    return Err(io::Error::new(io::ErrorKind::InvalidData, "jump out of bounds"));
                }
                branches.push(src);
                sections.push(dest);
            }
            this.push(i);
        }
        sections.sort_unstable();
        sections.dedup();
        let mut branches = branches.into_iter();
        for i in &mut this {
            if let Instruction::Jump { addr }
            | Instruction::CJump { addr, .. }
            | Instruction::Try { catch_addr: addr, .. } = i
            {
                let src = branches.next().unwrap();
                let dest = src.wrapping_add_signed(*addr);
                let from = sections.partition_point(|&pos| pos < src - 1) as i32 - 1;
                let to = sections.partition_point(|&pos| pos < dest) as i32;
                *addr = to - from;
            }
        }
        let mut bytepos = (0..this.len() as u32).zip(bytepos);
        for pos in &mut sections {
            (*pos, _) = bytepos
                .find(|(_, x)| *x == *pos)
                .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "jump to invalid address"))?;
        }
        Ok(Self { this, sections })
    }
}

#[derive(Debug, Clone, Default)]
pub struct Function {
    pub prologue: Box<[Addr]>,
    pub epilogue: Box<[Addr]>,
    pub entries: Box<[(Addr, StrIndex)]>,
}

impl Function {
    pub fn read(source: &mut impl io::Read, ctx: &mut CotophaData) -> io::Result<Self> {
        let ret = Self {
            prologue: source.read_data()?,
            epilogue: source.read_data()?,
            entries: source.read_value().and_then(|len: u32| {
                let mut v = Vec::with_capacity(len as usize);
                let r = (0..len).try_for_each(|_| Ok(v.push((source.read_data()?, StrIndex::read(source, ctx)?))));
                r.map(|_| v.into_boxed_slice())
            })?,
        };
        if !ret.prologue.is_sorted() || !ret.epilogue.is_sorted() {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "unsorted prologue/epilogue"));
        }
        if !ret.entries.is_sorted_by_key(|&(_, ix)| &ctx.strings[ix]) {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "unsorted functions"));
        }
        Ok(ret)
    }
}

#[derive(Debug, Clone, Default)]
pub struct Storage<const M: bool> {
    pub this: Box<[Var]>,
    pub num: u32,
}

impl<const M: bool> Storage<M> {
    pub fn read(source: &mut impl io::Read, ctx: &mut CotophaData) -> io::Result<Self> {
        let mut this = vec![];
        let Len(num) = source.read_value()?;
        Self::read_impl(&mut this, source, ctx, ArrIndex(..num), !M)?;
        let this = this.into_boxed_slice();
        Ok(Self { this, num })
    }

    fn read_impl(
        this: &mut Vec<Var>,
        source: &mut impl io::Read,
        ctx: &mut CotophaData,
        range: ArrIndex,
        alt: bool,
    ) -> io::Result<()> {
        this.resize_with(this.len().max(range.end as usize), Var::default);
        let mut start = this.len() as u32;
        for i in range.start..range.end {
            let name = StrIndex::read(source, ctx)?;
            let value = 'v: {
                if alt {
                    if let Ok(Len(len)) = source.read_value() {
                        let aix = ArrIndex(start..start + len);
                        start = aix.end;
                        Self::read_impl(this, source, ctx, aix, false)?;

                        break 'v Val::Array(aix);
                    }
                }
                let ty = source.read_value()?;
                exhaust(&mut source.take(3))?;
                match ty {
                    Type::Object => Val::Other { sp: StrIndex::read(source, ctx)? },
                    Type::Reference => Val::Other { sp: StrIndex::REFERENCE },
                    Type::Array => {
                        let Len(len) = source.read_value()?;
                        let aix = ArrIndex(start..start + len);
                        start = aix.end;
                        Self::read_impl(this, source, ctx, aix, false)?;

                        Val::Array(aix)
                    }
                    Type::Hash => Val::Other { sp: StrIndex::HASH },
                    Type::Integer => Val::Integer(source.read_value()?),
                    Type::Real => Val::Real(source.read_value()?),
                    Type::String => Val::String { ix: StrIndex::read(source, ctx)? },
                }
            };
            this[i as usize] = Var { name, value };
        }

        Ok(())
    }
}

pub struct ConstStr {
    pub conststr: Box<[StrIndex]>,
}

impl ConstStr {
    pub fn read(source: &mut impl io::Read, ctx: &mut CotophaData) -> io::Result<Self> {
        let Len(len) = source.read_value()?;
        let mut v = Vec::with_capacity(len as usize);
        for _ in 0..len {
            v.push(StrIndex::read(source, ctx)?);
            let Len(len) = source.read_value()?;
            exhaust(&mut source.take(4 * len as u64))?;
        }
        Ok(Self { conststr: v.into_boxed_slice() })
    }
}

#[non_exhaustive]
pub struct LinkInf {}

impl LinkInf {
    pub fn read(source: &mut impl io::Read, _: &mut CotophaData) -> io::Result<Self> {
        for _ in 0..4 {
            Reserved::Zero = source.read_value()?;
        }
        Ok(Self {})
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Addr(pub i32);

impl BinaryData for Addr {
    fn read(source: &mut impl io::Read) -> io::Result<Self> {
        Ok(Self(source.read_value()?))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct ArrIndex {
    pub start: u32,
    pub end: u32,
}

impl ArrIndex {
    pub fn len(self) -> u32 {
        self.end.saturating_sub(self.start)
    }

    fn read_args(source: &mut impl io::Read, ctx: &mut CotophaData) -> io::Result<Self> {
        let start = ctx.args.len() as u32;
        let Len(argc) = source.read_value()?;
        for i in 0..argc {
            Arg::read(source, ctx)?;
            if i < argc - 1 {
                ctx.strings.push_str(", ");
            }
        }
        let end = ctx.args.len() as u32;
        Ok(Self { start, end })
    }
}

#[expect(non_snake_case)]
pub fn ArrIndex(value: impl Into<ArrIndex>) -> ArrIndex {
    value.into()
}

impl From<Range<u32>> for ArrIndex {
    fn from(Range { start, end }: Range<u32>) -> Self {
        Self { start, end }
    }
}

impl From<RangeTo<u32>> for ArrIndex {
    fn from(RangeTo { end }: RangeTo<u32>) -> Self {
        Self { start: 0, end }
    }
}

impl<T> Index<ArrIndex> for Vec<T> {
    type Output = [T];

    fn index(&self, index: ArrIndex) -> &Self::Output {
        &(&**self)[index.start as usize..index.end as usize]
    }
}

impl<T> Index<ArrIndex> for Box<[T]> {
    type Output = [T];

    fn index(&self, index: ArrIndex) -> &Self::Output {
        &(&**self)[index.start as usize..index.end as usize]
    }
}

impl<T> Index<ArrIndex> for [T] {
    type Output = [T];

    fn index(&self, index: ArrIndex) -> &Self::Output {
        &self[index.start as usize..index.end as usize]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct StrIndex {
    pub start: u32,
    pub end: u32,
}

#[expect(non_snake_case)]
pub fn StrIndex(value: &[Arg]) -> StrIndex {
    if value.is_empty() {
        return StrIndex { start: 0, end: 0 };
    }
    let start = value[0].class.start;
    let end = value[value.len() - 1].name.end;
    StrIndex { start, end }
}

impl StrIndex {
    pub const REFERENCE: Self = Self { start: 0, end: 9 };
    pub const ARRAY: Self = Self { start: 9, end: 14 };
    pub const HASH: Self = Self { start: 14, end: 18 };
    pub const INTEGER: Self = Self { start: 18, end: 25 };
    pub const REAL: Self = Self { start: 25, end: 29 };
    pub const STRING: Self = Self { start: 29, end: 35 };

    pub const fn is_empty(self) -> bool {
        self.start >= self.end
    }
}

impl Index<StrIndex> for String {
    type Output = str;

    fn index(&self, index: StrIndex) -> &Self::Output {
        &self[index.start as usize..index.end as usize]
    }
}

impl StrIndex {
    pub fn read(source: &mut impl io::Read, ctx: &mut CotophaData) -> io::Result<Self> {
        let start = ctx.strings.len() as u32;
        let len: i32 = source.read_value()?;
        if len < 0 {
            return Ok(Self { start: len as u32, end: source.read_value()? });
        }
        let bytes = len.to_le_bytes();
        bytes.chain(source).read_into_data(&mut ctx.strings)?;
        let end = ctx.strings.len() as u32;
        Ok(Self { start, end })
    }
}

declare!(pub enum Type: u8 { Object, Reference, Array, Hash, Integer, Real, String });
declare!(pub enum Mode: u8 { Immediate, Stack, This, Global, Data, Auto });
declare!(pub enum MCreate: u8 { Stack = 1, This = 2 });
declare!(pub enum MLoad: u8 { Immediate, Stack, This, Global, Data });
declare!(pub enum MCall: u8 { This = 2, Global = 3, Auto = 5 });
declare!(pub enum Return: u8 { Normal, Void, TailCall });
declare!(pub enum Op: i8 { Nop = -1, Add, Sub, Mul, Div, Mod, And, Or, Xor, LogicalAnd, LogicalOr });
declare!(pub enum Uop: i8 { Plus, Negate, BitNot, LogicalNot });
declare!(pub enum Cmp: u8 { NotEqual, Equal, LessThan, LessEqual, GreaterThan, GreaterEqual });
declare!(pub enum InstructionCode: u8 { New, Free, Load, Store, Enter, Leave, Jump, CJump, Call, Return, Element, ElementIndirect, Operate, UniOperate, Compare });
declare!(enum TypeCode: u8 { Zero });
declare!(enum Throw: u16 { Valid = 0x0309 });

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub enum Immediate {
    Integer(i32),
    Real(f64),
    String(StrIndex),
    Nothing(Type, StrIndex),
}

impl Immediate {
    pub fn read(source: &mut impl io::Read, ctx: &mut CotophaData) -> io::Result<Self> {
        Ok(match source.read_value()? {
            Type::Integer => Self::Integer(source.read_value()?),
            Type::Real => Self::Real(source.read_value()?),
            Type::String => Self::String(StrIndex::read(source, ctx)?),
            ty => Self::Nothing(ty, read_class(source, ctx, ty)?),
        })
    }
}

pub fn read_class(source: &mut impl io::Read, ctx: &mut CotophaData, ty: Type) -> io::Result<StrIndex> {
    Ok(match ty {
        Type::Object => StrIndex::read(source, ctx)?,
        Type::Reference => StrIndex::REFERENCE,
        Type::Array => StrIndex::ARRAY,
        Type::Hash => StrIndex::HASH,
        Type::Integer => StrIndex::INTEGER,
        Type::Real => StrIndex::REAL,
        Type::String => StrIndex::STRING,
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Arg {
    pub ty: Type,
    pub class: StrIndex,
    pub name: StrIndex,
}

impl Arg {
    pub fn read(source: &mut impl io::Read, ctx: &mut CotophaData) -> io::Result<()> {
        let ty = source.read_value()?;
        let mut class = read_class(source, ctx, ty)?;
        if ty != Type::Object {
            let typename = &STRINGS[class.start as usize..class.end as usize];
            class.start = ctx.strings.len() as u32;
            ctx.strings += typename;
            class.end = ctx.strings.len() as u32;
        }
        ctx.strings.push(' ');
        let name = StrIndex::read(source, ctx)?;
        ctx.args.push(Arg { ty, class, name });
        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Val {
    Array(ArrIndex),
    Integer(i32),
    Real(f64),
    String { ix: StrIndex },
    Other { sp: StrIndex },
}

impl Default for Val {
    fn default() -> Self {
        Self::Array(ArrIndex { start: 0, end: 0 })
    }
}

impl Val {
    pub const fn is_default(self) -> bool {
        match self {
            Val::Array(aix) => aix.end == aix.start,
            Val::String { ix } => ix.end == ix.start,
            Val::Integer(0) | Val::Real(0.0) | Val::Other { .. } => true,
            _ => false,
        }
    }

    pub const fn class(self) -> StrIndex {
        match self {
            Val::Array(..) => StrIndex::ARRAY,
            Val::Integer(_) => StrIndex::INTEGER,
            Val::Real(_) => StrIndex::REAL,
            Val::String { .. } => StrIndex::STRING,
            Val::Other { sp } => sp,
        }
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct Var {
    pub name: StrIndex,
    pub value: Val,
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub enum Instruction {
    New { mode: MCreate, ty: Type, class: StrIndex, name: StrIndex },
    Free,
    Load { mode: MLoad, im: Immediate },
    Store { op: Op },
    Enter { name: StrIndex, args: ArrIndex },
    Return { free_stack: Return },
    Leave,
    Element { im: Immediate },
    ElementIndirect,
    Operate { op: Op },
    UniOperate { uop: Uop },
    Compare { cmp: Cmp },
    Jump { addr: i32 },
    CJump { logic: bool, addr: i32 },
    Call { mode: MCall, name: StrIndex, arg_num: u32 },
    Try { name: StrIndex, catch_addr: i32 },
    Throw { name: StrIndex, arg_num: u32 },
}
