//! Composition and decomposition of floats to and from a sign, an exponent, and a mantissa.

#![no_std]

pub trait FloatExt: Copy + Sized {
    const SIGN_SHIFT: u32;

    const EXP_MASK: Self::Bits;
    const EXP_BIAS: u32;
    const EXP_SHIFT: u32;

    const MANT_MASK: Self::Bits;
    const MANT_SHIFT: u32;

    type Bits: Copy;

    /// Composes a float from sign, exponent, and mantissa parts.
    fn from_parts(sign: Sign, exp: Exponent, mant: Mantissa) -> Self {
        Self::from_raw_parts(sign.to_sign_bit(), exp.biased, mant.0)
    }

    /// Decomposes `self` to a (sign, exponent, mantissa) tuple.
    fn to_parts(self) -> (Sign, Exponent, Mantissa) {
        let (neg, exp, mant) = self.to_raw_parts();
        (
            Sign::from_sign_bit(neg),
            Exponent {
                biased: exp,
                bias: Self::EXP_BIAS,
            },
            Mantissa(mant),
        )
    }

    /// Composes a float from raw sign, exponent, and mantissa parts.
    fn from_raw_parts(neg: bool, exp: u32, mant: u64) -> Self;

    /// Decomposes `self` to a raw (sign, exponent, mantissa) tuple.
    fn to_raw_parts(self) -> (bool, u32, u64) {
        (self.raw_sign(), self.raw_exponent(), self.raw_mantissa())
    }

    /// Returns the sign bit as a boolean.
    fn raw_sign(self) -> bool;

    /// Returns the biased exponent as an integer.
    fn raw_exponent(self) -> u32;

    /// Returns the mantissa as an integer.
    fn raw_mantissa(self) -> u64;

    /// Returns the sign.
    fn sign(self) -> Sign {
        Sign::from_sign_bit(self.raw_sign())
    }

    /// Returns the mantissa.
    fn mantissa(self) -> Mantissa {
        Mantissa(self.raw_mantissa())
    }

    /// Returns the exponent
    fn exponent(self) -> Exponent {
        Exponent {
            biased: self.raw_exponent(),
            bias: Self::EXP_BIAS,
        }
    }
}

/// Represents the sign of a floating-point number.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum Sign {
    Pos = 0,
    Neg = 1,
}

/// Represents the exponent part of a floating-point number.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Exponent {
    biased: u32,
    bias: u32,
}

/// Represents the mantissa (significand) part of a floating-point number.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
// TODO u64 too small for f128
pub struct Mantissa(u64);

impl Sign {
    pub fn from_sign_bit(neg: bool) -> Self {
        if neg {
            Self::Neg
        } else {
            Self::Pos
        }
    }
    pub fn to_sign_bit(self) -> bool {
        self == Self::Neg
    }
}

impl Exponent {
    pub fn biased(&self) -> u32 {
        self.biased
    }
    pub fn unbiased(&self) -> u32 {
        self.biased() - self.bias
    }
}

impl FloatExt for f32 {
    const SIGN_SHIFT: u32 = 31;

    const EXP_MASK: Self::Bits = ((1 << 8) - 1) << Self::EXP_SHIFT;
    const EXP_BIAS: u32 = 128;
    const EXP_SHIFT: u32 = 23;

    const MANT_MASK: Self::Bits = ((1 << 23) - 1) << Self::MANT_SHIFT;
    const MANT_SHIFT: u32 = 0;

    type Bits = u32;

    fn from_raw_parts(neg: bool, exp: u32, mant: u64) -> Self {
        let sign = u32::from(neg) << Self::SIGN_SHIFT;
        let exp = (exp << Self::EXP_SHIFT) & Self::EXP_MASK;
        let mant = (mant << Self::MANT_SHIFT) as u32 & Self::MANT_MASK;
        Self::from_bits(sign | exp | mant)
    }

    #[inline]
    fn raw_sign(self) -> bool {
        (self.to_bits() >> Self::SIGN_SHIFT) & 1 != 0
    }
    #[inline]
    fn raw_exponent(self) -> u32 {
        (self.to_bits() & Self::EXP_MASK) >> Self::EXP_SHIFT
    }
    #[inline]
    fn raw_mantissa(self) -> u64 {
        ((self.to_bits() & Self::MANT_MASK) >> Self::MANT_SHIFT).into()
    }
}

impl FloatExt for f64 {
    const SIGN_SHIFT: u32 = 63;

    const EXP_MASK: u64 = ((1 << 11) - 1) << Self::EXP_SHIFT;
    const EXP_BIAS: u32 = 1024;
    const EXP_SHIFT: u32 = 52;

    const MANT_MASK: u64 = ((1 << 52) - 1) << Self::MANT_SHIFT;
    const MANT_SHIFT: u32 = 0;

    type Bits = u64;

    fn from_raw_parts(neg: bool, exp: u32, mant: u64) -> Self {
        let sign = u64::from(neg) << Self::SIGN_SHIFT;
        let exp = (u64::from(exp) << Self::EXP_SHIFT) & Self::EXP_MASK;
        let mant = (mant << Self::MANT_SHIFT) & Self::MANT_MASK;
        Self::from_bits(sign | exp | mant)
    }

    #[inline]
    fn raw_sign(self) -> bool {
        (self.to_bits() >> Self::SIGN_SHIFT) & 1 != 0
    }
    #[inline]
    fn raw_exponent(self) -> u32 {
        ((self.to_bits() & Self::EXP_MASK) >> Self::EXP_SHIFT)
            .try_into()
            .expect("11-bit exponent fits in u32")
    }
    #[inline]
    fn raw_mantissa(self) -> u64 {
        (self.to_bits() & Self::MANT_MASK) >> Self::MANT_SHIFT
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::hint::black_box;

    #[test]
    fn f32_round_trip() {
        for i in 0..=u32::MAX {
            let f = black_box(f32::from_bits(i));
            let (s, m, e) = f.to_parts();
            let g = black_box(f32::from_parts(s, m, e));
            assert_eq!(
                f.to_bits(),
                g.to_bits(),
                "{f:?} != {g:?}\n(i=0x{i:0>8x}, subnorm={}, inf={}, nan={}, f={:?}, g={:?})",
                f.is_subnormal(),
                f.is_nan(),
                f.is_infinite(),
                f.to_parts(),
                g.to_parts(),
            );
        }
    }
    #[test]
    fn f64_round_trip() {
        for i in (0..=u64::MAX).step_by(0x01_00_00_00_00) {
            let f = black_box(f64::from_bits(i));
            let (s, m, e) = f.to_parts();
            let g = black_box(f64::from_parts(s, m, e));
            assert_eq!(
                f.to_bits(),
                g.to_bits(),
                "{f} != {g}\n(i=0x{i:0>16x}, subnorm={}, inf={}, nan={}, f={:?}, g={:?})",
                f.is_subnormal(),
                f.is_nan(),
                f.is_infinite(),
                f.to_parts(),
                g.to_parts(),
            );
        }
    }
}
