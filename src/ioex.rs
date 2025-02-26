use std::io;
use std::fmt;
use std::fmt::Write as _;

macro_rules! impl_from_bytes {
    ($($T:ty)*) => {
        $(impl TryFromBytes for $T {
            type Bytes = [u8; size_of::<Self>()];
            const ZEROED: Self::Bytes = [0; size_of::<Self>()];
            fn try_from_le_bytes(bytes: Self::Bytes) -> io::Result<Self> {
                Ok(Self::from_le_bytes(bytes))
            }
        })*
    };
}

impl_from_bytes!(i8 u8 i16 u16 i32 u32);

struct Written(usize);

impl fmt::Write for Written {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0 += s.len();
        Ok(())
    }
}

fn fmt_len(x: f64) -> usize {
    let mut w = Written(0);
    write!(w, "{x}").unwrap();
    w.0
}

impl TryFromBytes for f64 {
    type Bytes = [u8; size_of::<Self>()];
    const ZEROED: Self::Bytes = [0; size_of::<Self>()];
    fn try_from_le_bytes(bytes: Self::Bytes) -> io::Result<Self> {
        let r = Self::from_le_bytes(bytes);
        if !r.is_normal() || r == 0.0 {
            return Ok(r);
        }
        
        let x = r.abs();
        let xb = x.to_bits();
        let yb = xb - 1;
        let y = f64::from_bits(yb);
    
        match fmt_len(x) > fmt_len(y) {
            true => Ok(y.copysign(r)),
            false => Ok(r),
        }
    }
}

pub trait TryFromBytes: Sized {
    type Bytes: AsRef<[u8]> + AsMut<[u8]>;
    const ZEROED: Self::Bytes;
    fn try_from_le_bytes(bytes: Self::Bytes) -> io::Result<Self>;
}

impl TryFromBytes for bool {
    type Bytes = [u8; 1];
    const ZEROED: Self::Bytes = [0];
    fn try_from_le_bytes([byte]: Self::Bytes) -> io::Result<Self> {
        match byte {
            0 => Ok(false),
            1 => Ok(true),
            2.. => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("expected bool (0 or 1), found {byte:#x}"),
            )),
        }
    }
}

impl<const N: usize> TryFromBytes for [u8; N] {
    type Bytes = Self;
    const ZEROED: Self::Bytes = [0; N];
    fn try_from_le_bytes(bytes: Self::Bytes) -> io::Result<Self> {
        Ok(bytes)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Len(pub u32);

impl TryFromBytes for Len {
    type Bytes = [u8; 4];
    const ZEROED: Self::Bytes = [0; 4];

    fn try_from_le_bytes(bytes: Self::Bytes) -> io::Result<Self> {
        match i32::try_from_le_bytes(bytes)? {
            x @ 0.. => Ok(Self(x as u32)),
            _ => Err(io::Error::new(io::ErrorKind::InvalidData, "len is less than 0")),
        }
    }
}

#[macro_export]
macro_rules! declare {
    ($v:vis enum $Name:ident: $repr:ident { $Variant0:ident $(= $discr0:expr)?$(, $Variant:ident $(= $discr:expr)?)*$(,)? }) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #[repr($repr)]
        $v enum $Name {
            $Variant0 $(= $discr0)*,
            $($Variant $(= $discr)*),*
        }

        impl $crate::ioex::TryFromBytes for $Name {
            type Bytes = [u8; size_of::<Self>()];
            const ZEROED: Self::Bytes = [0; size_of::<Self>()];
            fn try_from_le_bytes(bytes: Self::Bytes) -> ::std::io::Result<Self> {
                let repr = <$repr>::try_from_le_bytes(bytes)?;
                if repr == Self::$Variant0 as $repr {
                    Ok(Self::$Variant0)
                } $(else if repr == Self::$Variant as $repr {
                    Ok(Self::$Variant)
                })* else {
                    Err(::std::io::Error::new(
                        ::std::io::ErrorKind::InvalidData,
                        format!(::std::concat!("invalid bit pattern {:#x} for type ", stringify!($Name)), repr)
                    ))
                }
            }
        }
    };
    ($v:vis struct $Name:ident = $bytes:literal) => {
        $v struct $Name;

        impl $crate::ioex::TryFromBytes for $Name {
            type Bytes = [u8; $bytes.len()];
            const ZEROED: Self::Bytes = [0; $bytes.len()];
            fn try_from_le_bytes(bytes: Self::Bytes) -> ::std::io::Result<Self> {
                match &bytes {
                    $bytes => Ok(Self),
                    err => Err(::std::io::Error::new(
                        ::std::io::ErrorKind::InvalidData,
                        format!(::std::concat!("invalid string \"{}\" for type ", stringify!($Name)), err.escape_ascii())
                    ))
                }
            }
        }
    };
}

pub trait BinaryData: Sized {
    fn read(source: &mut impl io::Read) -> io::Result<Self>;

    fn read_from(&mut self, source: &mut impl io::Read) -> io::Result<()> {
        *self = Self::read(source)?;
        Ok(())
    }
}

impl BinaryData for String {
    fn read(source: &mut impl io::Read) -> io::Result<Self> {
        let mut ret = String::new();
        ret.read_from(source)?;
        Ok(ret)
    }

    fn read_from(&mut self, source: &mut impl io::Read) -> io::Result<()> {
        let Len(len) = source.read_value()?;
        let mut err = None;
        let iter = (0..len).map_while(|_| match source.read_value() {
            Ok(codepoint) => Some(codepoint),
            Err(e) => err.replace(e).map(|_| 0),
        });

        let mut decode = None;
        for ch in char::decode_utf16(iter) {
            match ch {
                Ok(ch) => self.push(ch),
                Err(dec) => {
                    decode = Some(dec);
                    break;
                }
            }
        }

        if let Some(err) = err {
            Err(err)
        } else if let Some(decode) = decode {
            Err(io::Error::new(io::ErrorKind::InvalidData, decode))
        } else {
            Ok(())
        }
    }
}

impl<T: BinaryData> BinaryData for Vec<T> {
    fn read(source: &mut impl io::Read) -> io::Result<Self> {
        let mut ret = Vec::new();
        ret.read_from(source)?;
        Ok(ret)
    }

    fn read_from(&mut self, source: &mut impl io::Read) -> io::Result<()> {
        let Len(len) = source.read_value()?;
        self.reserve(len as usize);
        for _ in 0..len {
            self.push(source.read_data()?);
        }
        Ok(())
    }
}

impl<T: BinaryData> BinaryData for Box<[T]> {
    fn read(source: &mut impl io::Read) -> io::Result<Self> {
        Vec::read(source).map(Vec::into_boxed_slice)
    }
}

impl<T: BinaryData, U: BinaryData> BinaryData for (T, U) {
    fn read(source: &mut impl io::Read) -> io::Result<Self> {
        Ok((source.read_data()?, source.read_data()?))
    }
}

pub trait ReadEx: io::Read + Sized {
    fn try_read_value<T: TryFromBytes>(&mut self) -> io::Result<Option<T>> {
        let mut bytes = T::ZEROED;
        let read = self.read(bytes.as_mut())?;
        if read != bytes.as_ref().len() {
            return match read {
                0 => Ok(None),
                _ => Err(io::ErrorKind::UnexpectedEof.into()),
            };
        }
        Ok(Some(T::try_from_le_bytes(bytes)?))
    }

    fn read_value<T: TryFromBytes>(&mut self) -> io::Result<T> {
        let mut bytes = T::ZEROED;
        self.read_exact(bytes.as_mut())?;
        T::try_from_le_bytes(bytes)
    }

    fn read_data<T: BinaryData>(&mut self) -> io::Result<T> {
        T::read(self)
    }

    fn read_into_data<T: BinaryData>(&mut self, data: &mut T) -> io::Result<()> {
        data.read_from(self)
    }
}

impl<R: io::Read> ReadEx for R {}

pub fn exhaust(source: &mut io::Take<impl io::Read>) -> io::Result<()> {
    let limit = source.limit();
    let read = io::copy(source, &mut io::sink())?;
    if limit != read {
        return Err(io::ErrorKind::UnexpectedEof.into());
    }
    Ok(())
}
