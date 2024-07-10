use boojum::gadgets::{
    non_native_field::traits::NonNativeField, traits::hardexp_compatible::HardexpCompatible,
};

use super::*;

/// Curve parameter for the BN256 curve
const CURVE_U_PARAMETER: u64 = 4965661367192848881;

/// Curve parameter WNAF decomposition
pub const U_WNAF: [i8; 63] = [
    1, 0, 0, 0, 1, 0, 1, 0, 0, -1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0,
    0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0,
    1,
];

/// Method for calculating the hard part of the exponentiation
pub enum HardExpMethod {
    Naive,
    FuentesCastaneda,
    Devegili,
}

/// Compression approach before the hard part of the exponentiation
pub enum CompressionMethod {
    None,
    AlgebraicTorus,
}

/// Struct representing results of the final exponentiation evaluation
pub struct FinalExpEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    pub(super) resultant_f: BN256Fq12NNField<F>,
    _marker: std::marker::PhantomData<CS>,
}

impl<F, CS> FinalExpEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    /// Calculates the easy part of the exponentiation, that is
    /// `r^((p^(k) - 1) / Phi_k(p))` where
    /// `Phi_{12}(p) = p^4 - p^2 + 1` is a 12th cyclotomic polynomial.
    fn easy_part(cs: &mut CS, r: &mut BN256Fq12NNField<F>) -> BN256Fq12NNField<F> {
        // 1. f1 <- f1^*; 2. f2 <- f^{-1}; 3. f <- f1*f2; 4. f2 <- f
        let mut f1 = r.conjugate(cs);
        let mut f2 = r.inverse(cs);
        let mut r = f1.mul(cs, &mut f2);
        let mut f2 = r.clone();

        // 5. f <- f^q^2; 6. f <- f*f2;
        let mut r = r.frobenius_map(cs, 2);
        NonNativeField::normalize(&mut r, cs);
        let mut r = r.mul(cs, &mut f2);
        NonNativeField::normalize(&mut r, cs);

        r
    }

    /// This function computes the final exponentiation for the BN256 curve
    /// without using the Torus (`T2`) compression technique.
    ///
    /// The final exponentiation is partially based on _Algorithm 31_ from
    /// https://eprint.iacr.org/2010/354.pdf, but mainly based on implementation
    /// from pairing repository https://github.com/matter-labs/pairing.
    pub fn hard_part_naive<T>(cs: &mut CS, r: &mut T) -> T
    where
        T: HardexpCompatible<F>,
    {
        // Preparing a curve parameter
        let u = CURVE_U_PARAMETER;

        // 7-9. fpk <- f^p^k, k = 1, 2, 3
        let mut fp = r.frobenius_map(cs, 1);
        let mut fp2 = r.frobenius_map(cs, 2);
        let mut fp3 = fp2.frobenius_map(cs, 1);

        // 10-12. fuk <- f^u^k, k = 1, 2, 3
        r.normalize(cs);
        let mut fu = r.pow_u32(cs, &[u]);
        fu.normalize(cs);
        let mut fu2 = fu.pow_u32(cs, &[u]);
        fu2.normalize(cs);
        let mut fu3 = fu2.pow_u32(cs, &[u]);
        fu3.normalize(cs);

        // 13. y3 <- fu^p; 14. fu2p <- fu2^p; 15. fu3p <- fu3^p; 16. y2 <- fu2^p
        let mut y3 = fu.frobenius_map(cs, 1);
        let mut fu2p = fu2.frobenius_map(cs, 1);
        let mut fu3p = fu3.frobenius_map(cs, 1);
        let mut y2 = fu2.frobenius_map(cs, 2);
        y2.normalize(cs);

        // 17. y0 <- fp*fp2*fp3; 18. y1 <- r^*; 19. y5 <- fu2^*;
        fp.normalize(cs);
        fp2.normalize(cs);
        fp3.normalize(cs);
        let mut y0 = fp.mul(cs, &mut fp2);
        let mut y0 = y0.mul(cs, &mut fp3);
        let mut y1 = r.conjugate(cs);
        let mut y5 = fu2.conjugate(cs);

        // 20. y3 <- y3^*; 21. y4 <- fu*fu2p; 22. y4 <- y4^*;
        let mut y3 = y3.conjugate(cs);
        let mut y4 = fu.mul(cs, &mut fu2p);
        let mut y4 = y4.conjugate(cs);
        y4.normalize(cs);

        // 23. y6 <- fu3*fu3p; 24. y6 <- y6^*; 25. y6 <- y6^2;
        let mut y6 = fu3.mul(cs, &mut fu3p);
        let mut y6 = y6.conjugate(cs);
        y6.normalize(cs);
        let mut y6 = y6.square(cs);

        // 26. y6 <- y6*y4; 27. y6 <- y6*y5; 28. t1 <- y3*y5;
        let mut y6 = y6.mul(cs, &mut y4);
        let mut y6 = y6.mul(cs, &mut y5);
        let mut t1 = y3.mul(cs, &mut y5);
        t1.normalize(cs);

        // 29. t1 <- t1*y6; 30. y6 <- y6*y2; 31. t1 <- t1^2; 32. t1 <- t1*y6;
        let mut t1 = t1.mul(cs, &mut y6);
        let mut y6 = y6.mul(cs, &mut y2);
        t1.normalize(cs);
        let mut t1 = t1.square(cs);
        t1.normalize(cs);
        let mut t1 = t1.mul(cs, &mut y6);
        t1.normalize(cs);

        // 33. t1 <- t1^2; 34. t1 <- t1*y1; 35. t1 <- t1*y0;
        let mut t1 = t1.square(cs);
        t1.normalize(cs);
        let mut t0 = t1.mul(cs, &mut y1);
        let mut t1 = t1.mul(cs, &mut y0);
        t1.normalize(cs);

        // 36. t0 <- t0^2; 37. t0 <- t0*t1; Return t0
        t0.normalize(cs);
        let mut t0 = t0.square(cs);
        let mut t0 = t0.mul(cs, &mut t1);
        t0.normalize(cs);

        t0
    }

    /// This function computes the final exponentiation for the BN256 curve
    /// without using the Torus (`T2`) compression technique using the Fuentes-Castaneda method.
    pub fn hard_part_fuentes_castaneda<T>(cs: &mut CS, f: &mut T) -> T
    where
        T: HardexpCompatible<F>,
    {
        // Preparing a curve parameter
        let u = CURVE_U_PARAMETER;

        // 1-3. a <- f^u, a <- a^2, b <- a^2
        let mut a = f.pow_u32(cs, &[u]);
        a.normalize(cs);
        let mut a = a.square(cs);
        a.normalize(cs);
        let mut b = a.square(cs);
        b.normalize(cs);

        // 4-5. b <- a*b, t <- b^u
        let mut b = b.mul(cs, &mut a);
        b.normalize(cs);
        let mut t = b.pow_u32(cs, &[u]);
        t.normalize(cs);

        // 6. f <- f * frob(conj(f), 3)
        let mut tmp = f.conjugate(cs);
        let mut tmp = tmp.frobenius_map(cs, 3);
        let mut f = f.mul(cs, &mut tmp);
        f.normalize(cs);

        // 7-9. f <- f*t, b <- b*t, t <- t^2
        let mut f = f.mul(cs, &mut t);
        f.normalize(cs);
        let mut b = b.mul(cs, &mut t);
        b.normalize(cs);
        let mut t = t.square(cs);
        t.normalize(cs);

        // 10-12. t <- t^u, b <- b*t, t <- b*conj(a)
        let mut t = t.pow_u32(cs, &[u]);
        t.normalize(cs);
        let mut b = b.mul(cs, &mut t);
        b.normalize(cs);
        let mut tmp = a.conjugate(cs);
        let mut t = b.mul(cs, &mut tmp);
        t.normalize(cs);

        // 13-14. f <- f * frob(t, 3), f <- f * frob(t)
        let mut tmp = t.frobenius_map(cs, 3);
        let mut f = f.mul(cs, &mut tmp);
        f.normalize(cs);
        let mut tmp = t.frobenius_map(cs, 1);
        let mut f = f.mul(cs, &mut tmp);
        f.normalize(cs);

        // 15-16. f <- f * b, f <- f * frob(b, 2)
        let mut f = f.mul(cs, &mut b);
        f.normalize(cs);
        let mut tmp = b.frobenius_map(cs, 2);
        let mut f = f.mul(cs, &mut tmp);
        f.normalize(cs);

        f
    }

    /// This function computes the final exponentiation for the BN256 curve
    /// without using the Torus (`T2`) compression technique using the Devegili method.
    pub fn hard_part_devegili<T>(cs: &mut CS, f: &mut T) -> T
    where
        T: HardexpCompatible<F>,
    {
        // Preparing a curve parameter
        let u = CURVE_U_PARAMETER;

        // 1-3. a <- f^x, b <- a^2, a <- b * f^2
        let mut a = f.pow_u32(cs, &[u]);
        a.normalize(cs);
        let mut b = a.square(cs);
        b.normalize(cs);
        let mut f2 = f.square(cs);
        f2.normalize(cs);
        let mut a = b.mul(cs, &mut f2);
        a.normalize(cs);

        // 4-6. a <- a^2, a <- a*b, a <- a*f
        let mut a = a.square(cs);
        a.normalize(cs);
        let mut a = a.mul(cs, &mut b);
        let mut a = a.mul(cs, f);

        // 7-9. a <- conj(a), b <- frob(a), b <- a*b
        let mut a = a.conjugate(cs);
        a.normalize(cs);
        let mut b = a.frobenius_map(cs, 1);
        let mut b = a.mul(cs, &mut b);
        b.normalize(cs);

        // 10-12. a <- a*b, t0 <- frob(f), t1 <- t0*f
        let mut a = a.mul(cs, &mut b);
        let mut t0 = f.frobenius_map(cs, 1);
        let mut t1 = t0.mul(cs, f);
        t1.normalize(cs);

        // 13. t1 <- t1^9
        let mut tmp = t1.square(cs);
        tmp.normalize(cs);
        let mut tmp = tmp.square(cs);
        tmp.normalize(cs);
        let mut tmp = tmp.square(cs);
        tmp.normalize(cs);
        let mut t1 = tmp.mul(cs, &mut t1);
        t1.normalize(cs);

        // 14-16. a <- t1*a, t1 <- f^4, a <- a*t1
        let mut a = t1.mul(cs, &mut a);
        a.normalize(cs);
        let mut t1 = f2.square(cs);
        t1.normalize(cs);
        let mut a = a.mul(cs, &mut t1);

        // 17-19. t0 <- t0^2, b <- b*t0, t0 = frob(f, 2)
        let mut t0 = t0.square(cs);
        t0.normalize(cs);
        let mut b = b.mul(cs, &mut t0);
        b.normalize(cs);
        let mut t0 = f.frobenius_map(cs, 2);

        // 20-22. b <- b*t0, t0 <- b^x, t1 <- t0^2
        let mut b = b.mul(cs, &mut t0);
        b.normalize(cs);
        let mut t0 = b.pow_u32(cs, &[u]);
        t0.normalize(cs);
        let mut t1 = t0.square(cs);
        t1.normalize(cs);

        // 23-25. t0 <- t1^2, t0 <- t0*t1, t0 <- t0^x
        let mut t0 = t1.square(cs);
        t0.normalize(cs);
        let mut t0 = t0.mul(cs, &mut t1);
        t0.normalize(cs);
        let mut t0 = t0.pow_u32(cs, &[u]);
        t0.normalize(cs);

        // 26-27. t0 <- t0*b, a <- t0*a
        let mut t0 = t0.mul(cs, &mut b);
        t0.normalize(cs);
        let mut a = t0.mul(cs, &mut a);
        a.normalize(cs);

        // 28-29. t0 <- frob(f, 3), f <- t0*a
        let mut t0 = f.frobenius_map(cs, 3);
        t0.normalize(cs);
        let mut f = t0.mul(cs, &mut a);
        f.normalize(cs);

        f
    }

    /// This function computes the final exponentiation for the BN256 curve using the specified technique.
    /// It firstly computes the easy part as usual, then computes the hard part using one of the specified methods,
    /// and finally decompresses the result back to the `Fq12` element.
    pub fn evaluate(
        cs: &mut CS,
        r: &mut BN256Fq12NNField<F>,
        hardexp_method: HardExpMethod,
        compression_method: CompressionMethod,
    ) -> Self {
        let result = match compression_method {
            CompressionMethod::None => {
                let mut scalar = Self::easy_part(cs, r);
                match hardexp_method {
                    HardExpMethod::Naive => Self::hard_part_naive(cs, &mut scalar),
                    HardExpMethod::FuentesCastaneda => {
                        Self::hard_part_fuentes_castaneda(cs, &mut scalar)
                    }
                    HardExpMethod::Devegili => Self::hard_part_devegili(cs, &mut scalar),
                }
            }
            CompressionMethod::AlgebraicTorus => {
                let mut scalar = Self::easy_part(cs, r);
                let mut torus = BN256TorusWrapper::compress::<_, true>(cs, &mut scalar);
                let hard_part = match hardexp_method {
                    HardExpMethod::Naive => Self::hard_part_naive(cs, &mut torus),
                    HardExpMethod::FuentesCastaneda => {
                        Self::hard_part_fuentes_castaneda(cs, &mut torus)
                    }
                    HardExpMethod::Devegili => Self::hard_part_devegili(cs, &mut torus),
                };
                hard_part.decompress(cs)
            }
        };

        Self {
            resultant_f: result,
            _marker: std::marker::PhantomData::<CS>,
        }
    }

    /// Returns the accumulated `f` value after the final exponentiation.
    pub fn get(&self) -> BN256Fq12NNField<F> {
        self.resultant_f.clone()
    }
}
