use std::cmp::{Ordering, PartialOrd};
use std::fmt::{Display, Formatter, Result};
use std::ops::{Add, Div, Mul, Sub};

/// Base 10
#[derive(Clone)]
pub struct BigInt {
    /// stored in reverse
    val: Vec<i16>,
    neg: bool,
    significands: usize,
}

impl BigInt {
    pub fn zero() -> Self {
        Self {
            val: vec![0],
            neg: false,
            significands: 0,
        }
    }

    pub fn new(val: Vec<i16>, neg: bool) -> Self {
        // trim leading zeroes
        let mut val: Vec<i16> = val.into_iter().rev().skip_while(|n| n == &0).collect();
        val.reverse();
        let len = val.len();
        if len == 0 || (len == 1 && val.get(0).unwrap() == &0i16) {
            Self::zero()
        } else {
            Self {
                val,
                neg,
                significands: len,
            }
        }
    }

    pub fn from_str(s: &str) -> Self {
        if !s.is_ascii() {
            panic!();
        }

        let mut val = Vec::<i16>::new();
        let mut neg = false;
        for i in s.chars().into_iter().rev() {
            if neg {
                panic!("minus was not the first char");
            }
            if i == '-' {
                neg = true;
                continue;
            }
            if i == '_' {
                continue;
            }
            if !i.is_numeric() {
                panic!();
            }
            val.push(i.to_digit(10).unwrap() as i16);
        }

        Self::new(val, neg)
    }

    /// Note: Clones the vec containing the digits
    pub fn abs(&self) -> Self {
        Self::new(self.val.clone(), false)
    }

    /// abs() without cloning
    pub fn into_abs(self) -> Self {
        Self::new(self.val, false)
    }

    /// If both are equal, returns a
    pub fn max<'a>(a: &'a BigInt, b: &'a BigInt) -> &'a BigInt {
        if b > a {
            b
        } else {
            a
        }
    }

    /// If both are equal, returns a
    pub fn min<'a>(a: &'a BigInt, b: &'a BigInt) -> &'a BigInt {
        if b < a {
            b
        } else {
            a
        }
    }
}

impl PartialEq for BigInt {
    fn eq(&self, other: &Self) -> bool {
        if self.neg != other.neg {
            false
        } else if self.significands != other.significands {
            false
        } else {
            let mut a_iter = self.val.iter().rev();
            let mut b_iter = other.val.iter().rev();
            loop {
                let a_val = a_iter.next();
                let b_val = b_iter.next();
                if a_val.is_none() {
                    break true;
                }

                if -a_val.unwrap() > -b_val.unwrap() {
                    break false;
                } else if -b_val.unwrap() > -a_val.unwrap() {
                    break false;
                }
            }
        }
    }
}

impl PartialOrd for BigInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.significands > other.significands {
            Some(Ordering::Greater)
        } else if other.significands > self.significands {
            Some(Ordering::Less)
        } else if !self.neg && other.neg {
            Some(Ordering::Greater)
        } else if !other.neg && self.neg {
            Some(Ordering::Less)
        } else {
            let mut a_iter = self.val.iter().rev();
            let mut b_iter = other.val.iter().rev();
            if self.neg && other.neg {
                loop {
                    let a_val = a_iter.next();
                    let b_val = b_iter.next();
                    if a_val.is_none() {
                        // they are equal
                        break Some(Ordering::Equal);
                    }

                    if -a_val.unwrap() > -b_val.unwrap() {
                        break Some(Ordering::Greater);
                    } else if -b_val.unwrap() > -a_val.unwrap() {
                        break Some(Ordering::Less);
                    }
                }
            } else {
                loop {
                    let a_val = a_iter.next();
                    let b_val = b_iter.next();
                    if a_val.is_none() {
                        break Some(Ordering::Equal);
                    }
                    if a_val.unwrap() > b_val.unwrap() {
                        break Some(Ordering::Greater);
                    } else if b_val.unwrap() > a_val.unwrap() {
                        break Some(Ordering::Less);
                    }
                }
            }
        }
    }
}

impl Add for BigInt {
    type Output = BigInt;

    fn add(self, rhs: Self) -> Self::Output {
        // TODO: what even is this mess
        let mut res = Vec::<i16>::new();
        let neg : bool;
        let mut carry = 0i16;
        if (self.neg && rhs.neg) || (!self.neg && !rhs.neg) {
            neg = self.neg || rhs.neg;
            for i in 0..BigInt::max(&self, &rhs).significands {
                let mut tmp = carry;
                if let Some(l) = self.val.get(i) {
                    tmp += l;
                }
                if let Some(r) = rhs.val.get(i) {
                    tmp += r;
                }
                carry = tmp / 10;
                res.push(tmp % 10);
            }
        } else {
            // exclusive negative
            return if rhs.neg {
                self - rhs.into_abs()
            } else {
                rhs - self.into_abs()
            };
        }

        Self::new(res, neg)
    }
}

impl Sub for BigInt {
    type Output = BigInt;

    fn sub(self, rhs: Self) -> Self::Output {
        // TODO: what even is this mess
        let mut res = Vec::<i16>::new();
        let mut neg = false;
        let mut carry = 0i16;
        if !self.neg && !rhs.neg {
            // both positive
            if self == rhs {
                BigInt::from_str("0");
            }
            if self > rhs {
                for i in 0..BigInt::max(&self, &rhs).significands {
                    let mut tmp = -carry;
                    if let Some(l) = self.val.get(i) {
                        tmp += l;
                    }
                    if let Some(r) = rhs.val.get(i) {
                        tmp -= r;
                    }
                    if tmp >= 0 {
                        carry = 0;
                    } else {
                        carry = 1;
                    }
                    res.push((10 + tmp) % 10);
                }
            } else {
                neg = true;
                for i in 0..BigInt::max(&self, &rhs).significands {
                    let mut tmp = carry;
                    if let Some(l) = self.val.get(i) {
                        tmp += l;
                    }
                    if let Some(r) = rhs.val.get(i) {
                        tmp -= r;
                    }

                    if tmp > 0 {
                        tmp = 10 - tmp;
                        carry = 1;
                    } else {
                        carry = 0;
                    }
                    res.push(tmp.abs() % 10);
                }
            }
        } else {
            if rhs.neg && !self.neg {
                // left - -right = left + right
                return self + rhs.into_abs();
            } else if self.neg && !rhs.neg {
                // -left - right
                neg = true;
                for i in 0..BigInt::max(&self, &rhs).significands {
                    let mut tmp = carry; //carry;
                    if let Some(l) = self.val.get(i) {
                        tmp -= l;
                    }
                    if let Some(r) = rhs.val.get(i) {
                        tmp -= r;
                    }

                    carry = tmp / 10;
                    res.push(tmp.abs() % 10);
                }
            } else {
                // -left - -right = -left + right = right - left
                return rhs.into_abs() - self.into_abs();
            }
        }

        Self::new(res, neg)
    }
}

impl Mul for BigInt {
    type Output = BigInt;
    fn mul(self, rhs: Self) -> Self::Output {
        unimplemented!();
    }
}

impl Div for BigInt {
    type Output = BigInt;

    fn div(self, rhs: Self) -> Self::Output {
        unimplemented!()
    }
}

impl Display for BigInt {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        if self.neg {
            write!(f, "-")?;
        }
        for i in self.val.iter().rev() {
            write!(f, "{}", i)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn to_string() {
        let bigint = BigInt::from_str("1_327_448_559_661_077_911");
        assert_eq!("1327448559661077911", bigint.to_string());
    }

    #[test]
    fn to_string_neg() {
        let bigint = BigInt::from_str("-135_456_789_101_213");
        assert_eq!("-135456789101213", bigint.to_string());
    }

    #[test]
    fn significands() {
        let bigint = BigInt::from_str("1337");
        assert_eq!(4, bigint.significands);
    }

    mod bigint_add {
        use super::*;

        macro_rules! bigint_add_tests {
            ($($name:ident=>$value:expr,)*) => {
                $(
                    #[test]
                    fn $name() {
                        let a = BigInt::from_str($value.0);
                        let b = BigInt::from_str($value.1);
                        let result = a + b;
                        assert_eq!($value.2, result.to_string());
                    }
                )*
            };
        }

        bigint_add_tests!(
            zero_minus_zero => ("0", "0", "0"),
            neg_zero_minus_zero => ("-0", "0", "0"),
            zero_minus_neg_zero => ("0", "-0", "0"),
            neg_zero_minus_neg_zero => ("-0", "-0", "0"),
            pos_plus_neg => ("100", "-90", "10"),
            neg_plus_pos => ("-90", "100", "10"),
            pos_plus_neg_result_neg => ("100", "-900", "-800"),
            neg_plus_pos_result_neg => ("-900", "100", "-800"),
            no_carry => ("1", "2", "3"),
            no_carry_bigger => ("1_100_200_300_400", "2_200_300_400_501", "3300500700901"),
            no_carry_bigger_diff_significands => ("1_100_200_300_400", "2_200_300_400", "1102400600800"),
            no_carry_bigger_both_neg => ("-1_100_200_300_400", "-2_200_300_400_501", "-3300500700901"),
            no_carry_bigger_both_neg_diff_significands => ("-1_100_200_300_400", "-2_200_300_400", "-1102400600800"),
        );
    }

    mod bigint_sub {
        use super::*;

        macro_rules! bigint_sub_tests {
            ($($name:ident=>$value:expr,)*) => {
                $(
                    #[test]
                    fn $name() {
                        let a = BigInt::from_str($value.0);
                        let b = BigInt::from_str($value.1);
                        let result = a - b;
                        assert_eq!($value.2, result.to_string());
                    }
                )*
            };
        }

        bigint_sub_tests!(
            zero_minus_zero => ("0", "0", "0"),
            neg_zero_minus_zero => ("-0", "0", "0"),
            zero_minus_neg_zero => ("0", "-0", "0"),
            neg_zero_minus_neg_zero => ("-0", "-0", "0"),
            no_carry => ("457", "142", "315"),
            b_greater_than_a => ("457", "789", "-332"),
            carry_1 => ("457", "178", "279"),
            carry_1_diff_sign_count => ("4570", "178", "4392"),
            neg_minus_neg => ("-45703", "-17905", "-27798"),
            pos_minus_neg => ("45703", "-17905", "63608"),
            neg_minus_pos => ("-45703", "17905", "-63608"),
            something => ("-1_100_200_300_400", "2_200_300_400", "-1102400600800"),
        );
    }

    mod bigint_max {
        use super::*;

        macro_rules! bigint_max_tests {
            ($($name:ident=>$value:expr,)*) => {
                $(
                    #[test]
                    fn $name() {
                        let a = BigInt::from_str($value.0);
                        let b = BigInt::from_str($value.1);
                        let max = BigInt::max(&a,&b);
                        assert_eq!($value.2, max.to_string());
                    }
                )*
            };
        }

        bigint_max_tests!(
            both_neg_a_is_max => ("-2334", "-2414", "-2334"),
            both_neg_b_is_max => ("-233_400", "-233_100", "-233100"),
            equal_except_a_is_neg => ("-2334", "2334", "2334"),
            equal_except_b_is_neg => ("2334", "-2334", "2334"),
            same_significands_a_gt_b => ("2337", "1337", "2337"),
            same_significands_b_gt_a => ("1337", "2337", "2337"),
            same_significands_last_digit_differs_a_gt_b => ("1338", "1337", "1338"),
            same_significands_last_digit_differs_b_gt_a => ("1337", "1338", "1338"),
            diff_significands_a_gt_b => ("9_870_000", "12_222", "9870000"),
            diff_significands_b_gt_a => ("1_337", "21_359", "21359"),
        );
    }

    mod bigint_min {
        use super::*;

        macro_rules! bigint_min_tests {
            ($($name:ident=>$value:expr,)*) => {
                $(
                    #[test]
                    fn $name() {
                        let a = BigInt::from_str($value.0);
                        let b = BigInt::from_str($value.1);
                        let max = BigInt::min(&a,&b);
                        assert_eq!($value.2, max.to_string());
                    }
                )*
            };
        }

        bigint_min_tests!(
            both_neg_a_is_min => ("-2534", "-2414", "-2534"),
            both_neg_b_is_min => ("-233_400", "-233_439", "-233439"),
            equal_except_a_is_neg => ("-2334", "2334", "-2334"),
            equal_except_b_is_neg => ("2334", "-2334", "-2334"),
            same_significands_a_gt_b => ("2337", "1337", "1337"),
            same_significands_b_gt_a => ("1337", "2337", "1337"),
            same_significands_last_digit_differs_a_gt_b => ("1338", "1337", "1337"),
            same_significands_last_digit_differs_b_gt_a => ("1337", "1338", "1337"),
            diff_significands_a_gt_b => ("9_870_000", "12_222", "12222"),
            diff_significands_b_gt_a => ("1_337", "21_359", "1337"),
        );
    }
}

