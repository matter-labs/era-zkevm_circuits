use boojum::pairing::ff::BitIterator;
use boojum::pairing::ff::*;
use boojum::pairing::{
    EncodingBytes, GenericCompressedEncodable, GenericCurveAffine, GenericCurveProjective,
    GenericUncompressedEncodable, GroupDecodingError,
};

pub mod fq;
pub mod fr;

use fq::*;
use fr::*;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct PointAffine {
    pub(crate) x: Fq,
    pub(crate) y: Fq,
    pub(crate) infinity: bool,
}

static NAME_STR: &'static str = "Secp256r1";

impl ::std::fmt::Display for PointAffine {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        if self.infinity {
            write!(f, "{}(Infinity)", NAME_STR)
        } else {
            write!(f, "{}(x={}, y={})", NAME_STR, self.x, self.y)
        }
    }
}

#[derive(Copy, Clone, Debug, Eq)]
pub struct PointProjective {
    pub(crate) x: Fq,
    pub(crate) y: Fq,
    pub(crate) z: Fq,
}

impl ::std::fmt::Display for PointProjective {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "{}", self.into_affine())
    }
}

impl PartialEq for PointProjective {
    fn eq(&self, other: &PointProjective) -> bool {
        if self.is_zero() {
            return other.is_zero();
        }

        if other.is_zero() {
            return false;
        }

        // The points (X, Y, Z) and (X', Y', Z')
        // are equal when (X * Z^2) = (X' * Z'^2)
        // and (Y * Z^3) = (Y' * Z'^3).

        let mut z1 = self.z;
        z1.square();
        let mut z2 = other.z;
        z2.square();

        let mut tmp1 = self.x;
        tmp1.mul_assign(&z2);

        let mut tmp2 = other.x;
        tmp2.mul_assign(&z1);

        if tmp1 != tmp2 {
            return false;
        }

        z1.mul_assign(&self.z);
        z2.mul_assign(&other.z);
        z2.mul_assign(&self.y);
        z1.mul_assign(&other.y);

        if z1 != z2 {
            return false;
        }

        true
    }
}

impl PointAffine {
    fn mul_bits<S: AsRef<[u64]>>(&self, bits: BitIterator<S>) -> PointProjective {
        let mut res = PointProjective::zero();
        for i in bits {
            res.double();
            if i {
                res.add_assign_mixed(self)
            }
        }
        res
    }

    /// Attempts to construct an affine point given an x-coordinate. The
    /// point is not guaranteed to be in the prime order subgroup.
    ///
    /// If and only if `greatest` is set will the lexicographically
    /// largest y-coordinate be selected.
    fn get_point_from_x(_x: Fq, _greatest: bool) -> Option<PointAffine> {
        unimplemented!()
    }

    fn is_on_curve(&self) -> bool {
        if self.is_zero() {
            true
        } else {
            // Check that the point is on the curve
            let mut y2 = self.y;
            y2.square();

            let mut rhs = self.x;
            rhs.square();
            rhs.add_assign(&Self::get_coeff_a());
            rhs.mul_assign(&self.x);
            rhs.add_assign(&Self::get_coeff_b());

            y2 == rhs
        }
    }
}

impl GenericCurveAffine for PointAffine {
    type Scalar = Fr;
    type Base = Fq;
    type Projective = PointProjective;

    fn zero() -> Self {
        PointAffine {
            x: Fq::zero(),
            y: Fq::one(),
            infinity: true,
        }
    }

    fn one() -> Self {
        Self::get_generator()
    }

    fn is_zero(&self) -> bool {
        self.infinity
    }

    fn mul<S: Into<<Self::Scalar as PrimeField>::Repr>>(&self, by: S) -> PointProjective {
        let bits = BitIterator::new(by.into());
        self.mul_bits(bits)
    }

    fn negate(&mut self) {
        if !self.is_zero() {
            self.y.negate();
        }
    }

    fn into_projective(&self) -> PointProjective {
        (*self).into()
    }

    #[inline(always)]
    fn as_xy(&self) -> (&Self::Base, &Self::Base) {
        (&self.x, &self.y)
    }

    #[inline(always)]
    fn into_xy_unchecked(self) -> (Self::Base, Self::Base) {
        (self.x, self.y)
    }

    #[inline(always)]
    fn from_xy_unchecked(x: Self::Base, y: Self::Base) -> Self {
        let infinity = x.is_zero() && y.is_zero();
        Self {
            x: x,
            y: y,
            infinity,
        }
    }

    fn from_xy_checked(x: Self::Base, y: Self::Base) -> Result<Self, GroupDecodingError> {
        let infinity = x.is_zero() && y.is_zero();
        let affine = Self {
            x: x,
            y: y,
            infinity,
        };

        if !affine.is_on_curve() {
            Err(GroupDecodingError::NotOnCurve)
        } else {
            Ok(affine)
        }
    }

    fn a_coeff() -> Self::Base {
        Self::get_coeff_a()
    }

    fn b_coeff() -> Self::Base {
        Self::get_coeff_b()
    }
}

impl GenericCurveProjective for PointProjective {
    type Scalar = Fr;
    type Base = Fq;
    type Affine = PointAffine;

    // The point at infinity is always represented by
    // Z = 0.
    fn zero() -> Self {
        PointProjective {
            x: Fq::zero(),
            y: Fq::one(),
            z: Fq::zero(),
        }
    }

    fn one() -> Self {
        PointAffine::one().into()
    }

    // The point at infinity is always represented by
    // Z = 0.
    fn is_zero(&self) -> bool {
        self.z.is_zero()
    }

    fn is_normalized(&self) -> bool {
        self.is_zero() || self.z == Fq::one()
    }

    fn batch_normalization(v: &mut [Self]) {
        // Montgomery’s Trick and Fast Implementation of Masked AES
        // Genelle, Prouff and Quisquater
        // Section 3.2

        // First pass: compute [a, ab, abc, ...]
        let mut prod = Vec::with_capacity(v.len());
        let mut tmp = Fq::one();
        for g in v
            .iter_mut()
            // Ignore normalized elements
            .filter(|g| !g.is_normalized())
        {
            tmp.mul_assign(&g.z);
            prod.push(tmp);
        }

        // Invert `tmp`.
        tmp = tmp.inverse().unwrap(); // Guaranteed to be nonzero.

        // Second pass: iterate backwards to compute inverses
        for (g, s) in v
            .iter_mut()
            // Backwards
            .rev()
            // Ignore normalized elements
            .filter(|g| !g.is_normalized())
            // Backwards, skip last element, fill in one for last term.
            .zip(prod.into_iter().rev().skip(1).chain(Some(Fq::one())))
        {
            // tmp := tmp * g.z; g.z := tmp * s = 1/z
            let mut newtmp = tmp;
            newtmp.mul_assign(&g.z);
            g.z = tmp;
            g.z.mul_assign(&s);
            tmp = newtmp;
        }

        // Perform affine transformations
        for g in v.iter_mut().filter(|g| !g.is_normalized()) {
            let mut z = g.z; // 1/z
            z.square(); // 1/z^2
            g.x.mul_assign(&z); // x/z^2
            z.mul_assign(&g.z); // 1/z^3
            g.y.mul_assign(&z); // y/z^3
            g.z = Fq::one(); // z = 1
        }
    }

    fn double(&mut self) {
        if self.is_zero() {
            return;
        }

        // https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#doubling-dbl-2007-bl
        let mut xx = self.x;
        xx.square();
        let mut yy = self.y;
        yy.square();
        let mut yyyy = yy;
        yyyy.square();
        let mut zz = self.z;
        zz.square();
        let mut s = self.x;
        s.add_assign(&yy);
        s.square();
        s.sub_assign(&xx);
        s.sub_assign(&yyyy);
        s.double();

        let mut m1 = zz;
        m1.square();
        m1.mul_assign(&PointAffine::a_coeff());
        let mut m = xx;
        m.double();
        m.add_assign(&xx);
        m.add_assign(&m1);

        let mut two_s = s;
        two_s.double();

        let mut t = m;
        t.square();
        t.sub_assign(&two_s);

        self.x = t;

        let mut eight_yyyy = yyyy;
        eight_yyyy.double();
        eight_yyyy.double();
        eight_yyyy.double();

        let y1 = self.y;

        self.y = s;
        self.y.sub_assign(&t);
        self.y.mul_assign(&m);
        self.y.sub_assign(&eight_yyyy);

        self.z.add_assign(&y1);
        self.z.square();
        self.z.sub_assign(&yy);
        self.z.sub_assign(&zz);
    }

    fn add_assign(&mut self, _other: &Self) {
        unimplemented!()
    }

    fn add_assign_mixed(&mut self, other: &Self::Affine) {
        if other.is_zero() {
            return;
        }

        if self.is_zero() {
            self.x = other.x;
            self.y = other.y;
            self.z = Fq::one();
            return;
        }

        // http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-madd-2007-bl

        // Z1Z1 = Z1^2
        let mut z1z1 = self.z;
        z1z1.square();

        // U2 = X2*Z1Z1
        let mut u2 = other.x;
        u2.mul_assign(&z1z1);

        // S2 = Y2*Z1*Z1Z1
        let mut s2 = other.y;
        s2.mul_assign(&self.z);
        s2.mul_assign(&z1z1);

        if self.x == u2 && self.y == s2 {
            // The two points are equal, so we double.
            self.double();
        } else {
            // If we're adding -a and a together, self.z becomes zero as H becomes zero.

            // H = U2-X1
            let mut h = u2;
            h.sub_assign(&self.x);

            // HH = H^2
            let mut hh = h;
            hh.square();

            // I = 4*HH
            let mut i = hh;
            i.double();
            i.double();

            // J = H*I
            let mut j = h;
            j.mul_assign(&i);

            // r = 2*(S2-Y1)
            let mut r = s2;
            r.sub_assign(&self.y);
            r.double();

            // V = X1*I
            let mut v = self.x;
            v.mul_assign(&i);

            // X3 = r^2 - J - 2*V
            self.x = r;
            self.x.square();
            self.x.sub_assign(&j);
            self.x.sub_assign(&v);
            self.x.sub_assign(&v);

            // Y3 = r*(V-X3)-2*Y1*J
            j.mul_assign(&self.y); // J = 2*Y1*J
            j.double();
            self.y = v;
            self.y.sub_assign(&self.x);
            self.y.mul_assign(&r);
            self.y.sub_assign(&j);

            // Z3 = (Z1+H)^2-Z1Z1-HH
            self.z.add_assign(&h);
            self.z.square();
            self.z.sub_assign(&z1z1);
            self.z.sub_assign(&hh);
        }
    }

    fn negate(&mut self) {
        if !self.is_zero() {
            self.y.negate()
        }
    }

    fn mul_assign<S: Into<<Self::Scalar as PrimeField>::Repr>>(&mut self, other: S) {
        let mut res = Self::zero();

        let mut found_one = false;

        for i in BitIterator::new(other.into()) {
            if found_one {
                res.double();
            } else {
                found_one = i;
            }

            if i {
                res.add_assign(self);
            }
        }

        *self = res;
    }

    fn into_affine(&self) -> PointAffine {
        (*self).into()
    }

    fn recommended_wnaf_for_scalar(scalar: <Self::Scalar as PrimeField>::Repr) -> usize {
        Self::empirical_recommended_wnaf_for_scalar(scalar)
    }

    fn recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
        Self::empirical_recommended_wnaf_for_num_scalars(num_scalars)
    }

    fn as_xyz(&self) -> (&Self::Base, &Self::Base, &Self::Base) {
        (&self.x, &self.y, &self.z)
    }

    fn into_xyz_unchecked(self) -> (Self::Base, Self::Base, Self::Base) {
        (self.x, self.y, self.z)
    }

    fn from_xyz_unchecked(x: Self::Base, y: Self::Base, z: Self::Base) -> Self {
        Self { x, y, z }
    }

    fn from_xyz_checked(
        _x: Self::Base,
        _y: Self::Base,
        _z: Self::Base,
    ) -> Result<Self, GroupDecodingError> {
        unimplemented!()
    }
}

// The affine point X, Y is represented in the jacobian
// coordinates with Z = 1.
impl From<PointAffine> for PointProjective {
    fn from(p: PointAffine) -> PointProjective {
        if p.is_zero() {
            PointProjective::zero()
        } else {
            PointProjective {
                x: p.x,
                y: p.y,
                z: Fq::one(),
            }
        }
    }
}

// The projective point X, Y, Z is represented in the affine
// coordinates as X/Z^2, Y/Z^3.
impl From<PointProjective> for PointAffine {
    fn from(p: PointProjective) -> PointAffine {
        if p.is_zero() {
            PointAffine::zero()
        } else if p.z == Fq::one() {
            // If Z is one, the point is already normalized.
            PointAffine {
                x: p.x,
                y: p.y,
                infinity: false,
            }
        } else {
            // Z is nonzero, so it must have an inverse in a field.
            let zinv = p.z.inverse().unwrap();
            let mut zinv_powered = zinv;
            zinv_powered.square();

            // X/Z^2
            let mut x = p.x;
            x.mul_assign(&zinv_powered);

            // Y/Z^3
            let mut y = p.y;
            zinv_powered.mul_assign(&zinv);
            y.mul_assign(&zinv_powered);

            PointAffine {
                x: x,
                y: y,
                infinity: false,
            }
        }
    }
}

impl rand::Rand for PointProjective {
    fn rand<R: rand::Rng>(rng: &mut R) -> Self {
        loop {
            let x = rng.gen();
            let greatest = rng.gen();

            if let Some(p) = PointAffine::get_point_from_x(x, greatest) {
                if !p.is_zero() {
                    if p.is_on_curve() {
                        return p.into_projective();
                    }
                }
            }
        }
    }
}

impl rand::Rand for PointAffine {
    fn rand<R: rand::Rng>(rng: &mut R) -> Self {
        loop {
            let x = rng.gen();
            let greatest = rng.gen();

            if let Some(p) = PointAffine::get_point_from_x(x, greatest) {
                if !p.is_zero() {
                    if p.is_on_curve() {
                        return p;
                    }
                }
            }
        }
    }
}

impl PointAffine {
    fn get_coeff_a() -> <Self as GenericCurveAffine>::Base {
        crate::ff::from_hex::<Fq>(
            "0xffffffff00000001000000000000000000000000fffffffffffffffffffffffc",
        )
        .unwrap()
    }

    fn get_coeff_b() -> <Self as GenericCurveAffine>::Base {
        crate::ff::from_hex::<Fq>(
            "0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b",
        )
        .unwrap()
    }

    fn get_generator() -> Self {
        Self {
            x: crate::ff::from_hex::<Fq>(
                "0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296",
            )
            .unwrap(),
            y: crate::ff::from_hex::<Fq>(
                "0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5",
            )
            .unwrap(),
            infinity: false,
        }
    }
}

impl PointProjective {
    fn empirical_recommended_wnaf_for_scalar(scalar: FrRepr) -> usize {
        let num_bits = scalar.num_bits() as usize;

        if num_bits >= 130 {
            4
        } else if num_bits >= 34 {
            3
        } else {
            2
        }
    }

    fn empirical_recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
        const RECOMMENDATIONS: [usize; 12] =
            [1, 3, 7, 20, 43, 120, 273, 563, 1630, 3128, 7933, 62569];

        let mut ret = 4;
        for r in &RECOMMENDATIONS {
            if num_scalars > *r {
                ret += 1;
            } else {
                break;
            }
        }

        ret
    }
}

impl GenericUncompressedEncodable<64> for PointAffine {
    /// Converts this element into its uncompressed encoding, so long as it's not
    /// the point at infinity.
    fn into_uncompressed(&self) -> EncodingBytes<Self, 64> {
        todo!()
    }

    /// Converts an uncompressed encoding into the curve point
    fn from_uncompressed(_encoding: EncodingBytes<Self, 64>) -> Result<Self, GroupDecodingError> {
        todo!()
    }
}

impl GenericCompressedEncodable<32> for PointAffine {
    /// Converts this element into its uncompressed encoding, so long as it's not
    /// the point at infinity.
    fn into_compressed(&self) -> (EncodingBytes<Self, 32>, bool) {
        todo!();
    }

    /// Converts an uncompressed encoding into the curve point
    fn from_compressed(
        _encoding: EncodingBytes<Self, 32>,
        _parity: bool,
    ) -> Result<Self, GroupDecodingError> {
        todo!()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_trivial_mul() {
        let mut t1 = PointAffine::one().into_projective();
        t1.double();

        let mut tt = t1;
        let mut base = PointAffine::one();
        base.negate();
        tt.add_assign_mixed(&base);

        assert_eq!(tt.into_affine(), PointAffine::one());

        let mut t2 = PointAffine::one().into_projective();
        t2.add_assign_mixed(&PointAffine::one());

        assert_eq!(t1.into_affine(), t2.into_affine());

        let p = PointAffine::one();
        let result = p.mul(Fr::char());
        assert!(result.is_zero());
    }
}
