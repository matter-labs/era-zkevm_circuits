use std::sync::Arc;

use boojum::{
    gadgets::non_native_field::traits::NonNativeField,
    pairing::{bn256::{Fq2, FROBENIUS_COEFF_FQ6_C1, XI_TO_Q_MINUS_1_OVER_2}, ff::Field},
};
use final_exp::{CompressionMethod, FinalExpEvaluation, HardExpMethod};

use super::*;

// Curve parameter for the BN256 curve
const SIX_U_PLUS_TWO_WNAF: [i8; 65] = [
    0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 1, -1, 0, 0, 1, 0, 0, 1, 1, 0, -1, 0, 0, 1, 0, -1, 0, 0, 0, 0,
    1, 1, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0,
    0, 1, 0, 1, 1,
];

/// Struct for the line function evaluation for the BN256 curve (addition and doubling).
/// The line function is used in the Miller loop of the pairing function.
pub struct LineFunctionEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    c0: BN256Fq2NNField<F>,
    c3: BN256Fq2NNField<F>,
    c4: BN256Fq2NNField<F>,
    point: BN256SWProjectivePointTwisted<F>,
    _marker: std::marker::PhantomData<CS>,
}

impl<F, CS> LineFunctionEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    /// Creates a zero instance of the line function evaluation for the BN256 curve.
    pub fn zero(cs: &mut CS, params: &Arc<BN256BaseNNFieldParams>) -> Self {
        Self {
            c0: BN256Fq2NNField::zero(cs, params),
            c3: BN256Fq2NNField::zero(cs, params),
            c4: BN256Fq2NNField::zero(cs, params),
            point: BN256SWProjectivePointTwisted::zero(cs, params),
            _marker: std::marker::PhantomData::<CS>,
        }
    }

    /// Returns the point of the line function evaluation.
    pub fn point(&self) -> BN256SWProjectivePointTwisted<F> {
        self.point.clone()
    }

    /// Returns the coefficients of the line function evaluation.
    pub fn c0c3c4(&self) -> (BN256Fq2NNField<F>, BN256Fq2NNField<F>, BN256Fq2NNField<F>) {
        (self.c0.clone(), self.c3.clone(), self.c4.clone())
    }

    /// This function conducts the doubling step in the Miller loop for the BN256 curve.
    /// Namely, given `Q` in `E'(Fp2)` and `P` in `E(Fp)`, it computes the line function
    /// together with the resultant point `T=2*Q`. The implementation is based
    /// on the _Algorithm 26_ from https://eprint.iacr.org/2010/354.pdf.
    pub fn doubling_step(
        cs: &mut CS,
        q: &mut BN256SWProjectivePointTwisted<F>,
        p: &mut BN256SWProjectivePoint<F>,
    ) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // 1. tmp0 <- X_Q^2; 2. tmp1 <- Y_Q^2; 3. tmp2 <- tmp1^2;
        let mut tmp0 = q.x.square(cs);
        let mut tmp1 = q.y.square(cs);
        let mut tmp2 = tmp1.square(cs);

        // 4. tmp3 <- (tmp1 + X_Q)^2 - tmp0 - tmp2; 5. tmp3 <- 2*tmp3;
        let mut tmp3 = tmp1.add(cs, &mut q.x);
        let mut tmp3 = tmp3.square(cs);
        let mut tmp3 = tmp3.sub(cs, &mut tmp0);
        let mut tmp3 = tmp3.sub(cs, &mut tmp2);
        let mut tmp3 = tmp3.double(cs);

        // 6. tmp4 <- 3*tmp0; 7. tmp6 <- X_Q + tmp4;
        let mut tmp4 = tmp0.double(cs);
        let mut tmp4 = tmp4.add(cs, &mut tmp0);
        let mut tmp6 = q.x.add(cs, &mut tmp4);

        // 8. tmp5 <- tmp4^2; 9. X_T <- tmp5 - 2*tmp3;
        let mut tmp5 = tmp4.square(cs);
        let mut tmp3_double = tmp3.double(cs);
        let mut x_t = tmp5.sub(cs, &mut tmp3_double);

        // Saving Z_Q^2 for later use
        let mut z_q_square = q.z.square(cs);

        // 10. Z_T <- (Y_Q + Z_Q)^2 - tmp1 - Z_Q^2;
        let mut z_t = q.y.add(cs, &mut q.z);
        let mut z_t = z_t.square(cs);
        let mut z_t = z_t.sub(cs, &mut tmp1);
        let mut z_t = z_t.sub(cs, &mut z_q_square);

        // 11. Y_T <- (tmp3 - X_T)*tmp4 - 8*tmp2;
        let mut y_t = tmp3.sub(cs, &mut x_t);
        let mut y_t = y_t.mul(cs, &mut tmp4);
        let mut tmp2_8 = tmp2.double(cs);
        let mut tmp2_8 = tmp2_8.double(cs);
        let mut tmp2_8 = tmp2_8.double(cs);
        let y_t = y_t.sub(cs, &mut tmp2_8);

        // 12. tmp3 <- -2*(tmp4 * Z_Q^2); 13. tmp3 <- tmp3 * xP;
        let mut tmp3 = tmp4.mul(cs, &mut z_q_square);
        let mut tmp3 = tmp3.double(cs);
        let mut tmp3 = tmp3.negated(cs);
        let mut tmp3 = tmp3.mul_c0(cs, &mut p.x);
        tmp3.normalize(cs);

        // 14. tmp6 <- tmp6^2 - tmp0 - tmp5 - 4*tmp1; 15. tmp0 <- 2*Z_T*Z_Q^2
        let mut tmp6 = tmp6.square(cs);
        let mut tmp6 = tmp6.sub(cs, &mut tmp0);
        let mut tmp6 = tmp6.sub(cs, &mut tmp5);
        let mut tmp1_4 = tmp1.double(cs);
        let mut tmp1_4 = tmp1_4.double(cs);
        let tmp6 = tmp6.sub(cs, &mut tmp1_4);
        let mut tmp0 = z_t.mul(cs, &mut z_q_square);
        let mut tmp0 = tmp0.double(cs);

        // 16. tmp0 <- tmp0 * y_P
        let tmp0 = tmp0.mul_c0(cs, &mut p.y);

        // Result: T = (X_T, Y_T, Z_T); Line function is a0 + a1*w
        // where a0 = tmp0; a1 = tmp3 + tmp6*v;
        Self {
            c0: tmp0,
            c3: tmp3,
            c4: tmp6,
            point: BN256SWProjectivePointTwisted {
                x: x_t,
                y: y_t,
                z: z_t,
                _marker: std::marker::PhantomData,
            },
            _marker: std::marker::PhantomData,
        }
    }

    /// This function conducts the addition step in the Miller loop for the BN256 curve.
    /// Namely, given `Q` and `R` in `E'(Fp2)` and `P` in `E(Fp)`, it computes the line function
    /// together with the resultant point `T=Q+R`. The implementation is based
    /// on the _Algorithm 27_ from https://eprint.iacr.org/2010/354.pdf.
    pub fn addition_step(
        cs: &mut CS,
        q: &mut BN256SWProjectivePointTwisted<F>,
        r: &mut BN256SWProjectivePointTwisted<F>,
        p: &mut BN256SWProjectivePoint<F>,
    ) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // Preparing some temporary variables
        let mut z_r_square = r.z.square(cs);
        let mut y_q_square = q.y.square(cs);

        // 1. t0 <- X_Q*Z_R^2; 2. t1 <- (Y_Q + Z_R)^2 - Y_Q^2 - Z_R^2;
        let mut t0 = q.x.mul(cs, &mut z_r_square);
        let mut t1 = q.y.add(cs, &mut r.z);
        let mut t1 = t1.square(cs);
        let mut t1 = t1.sub(cs, &mut y_q_square);
        let mut t1 = t1.sub(cs, &mut z_r_square);

        // 3. t1 <- t1 * Z_R^2; 4. t2 <- t0 - X_R; 5. t3 <- t2^2;
        let mut t1 = t1.mul(cs, &mut z_r_square);
        let mut t2 = t0.sub(cs, &mut r.x);
        let mut t3 = t2.square(cs);

        // 6. t4 <- 4*t3; 7. t5 <- t4*t2; 8. t6 <- t1 - 2*Y_R;
        let mut t4 = t3.double(cs);
        let mut t4 = t4.double(cs);
        let mut t5 = t4.mul(cs, &mut t2);
        let mut y_r_2 = r.y.double(cs);
        let mut t6 = t1.sub(cs, &mut y_r_2);

        // 9. t9 <- t6 * X_Q; 10. t7 <- X_R * t4; 11. X_T <- t6^2 - t5 - 2t7
        let mut t9 = t6.mul(cs, &mut q.x);
        let mut t7 = r.x.mul(cs, &mut t4);
        let mut x_t = t6.square(cs);
        let mut x_t = x_t.sub(cs, &mut t5);
        let mut t7_2 = t7.double(cs);
        let mut x_t = x_t.sub(cs, &mut t7_2);

        // 12. Z_T <- (Z_R + t2)^2 - Z_R^2 - t3;
        let mut z_t = r.z.add(cs, &mut t2);
        let mut z_t = z_t.square(cs);
        let mut z_t = z_t.sub(cs, &mut z_r_square);
        let mut z_t = z_t.sub(cs, &mut t3);

        // 13. t10 <- Y_Q + Z_T; 14. t8 <- (t7 - X_T)*t6;
        let mut t10 = q.y.add(cs, &mut z_t);
        let mut t8 = t7.sub(cs, &mut x_t);
        let mut t8 = t8.mul(cs, &mut t6);

        // 15. t0 <- 2*Y_R*t5; 16. Y_T <- t8 - t0; 17. t10 <- t10^2 - Y_Q^2 - Z_T^2;
        let mut t0 = y_r_2.mul(cs, &mut t5);
        let y_t = t8.sub(cs, &mut t0);
        let mut t10 = t10.square(cs);
        let mut t10 = t10.sub(cs, &mut y_q_square);
        let mut z_t_square = z_t.square(cs);
        let mut t10 = t10.sub(cs, &mut z_t_square);

        // 18. t9 <- 2*t9 - t10; 19. t10 <- 2*Z_T*y_P;
        let mut t9 = t9.double(cs);
        let t9 = t9.sub(cs, &mut t10);
        let mut t10 = z_t.mul_c0(cs, &mut p.y);
        let t10 = t10.double(cs);

        // 20. t6 <- -t6; 21. t1 <- 2*t6*x_P;
        let mut t6 = t6.negated(cs);
        let mut t1 = t6.mul_c0(cs, &mut p.x);
        let t1 = t1.double(cs);

        // Result: T = (X_T, Y_T, Z_T); Line function is l0 + l1*w
        // where l0 = t10; l1 = t1 + t9*v;
        Self {
            c0: t10,
            c3: t1,
            c4: t9,
            point: BN256SWProjectivePointTwisted {
                x: x_t,
                y: y_t,
                z: z_t,
                _marker: std::marker::PhantomData,
            },
            _marker: std::marker::PhantomData,
        }
    }
}

/// Struct for the miller loop evaluation for the BN256 curve.
/// Here, the Miller loop returns the accumulated f value after the loop
/// without the final exponentiation.
pub struct MillerLoopEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    accumulated_f: BN256Fq12NNField<F>,
    _marker: std::marker::PhantomData<CS>,
}

impl<F, CS> MillerLoopEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    pub fn get_accumulated_f(&self) -> BN256Fq12NNField<F> {
        self.accumulated_f.clone()
    }

    /// This function computes the Miller loop for the BN256 curve, using
    /// _Algorithm 1_ from https://eprint.iacr.org/2010/354.pdf. Frobenius
    /// map is taken from https://hackmd.io/@Wimet/ry7z1Xj-2.
    pub fn evaluate(
        cs: &mut CS,
        p: &mut BN256SWProjectivePoint<F>,
        q: &mut BN256SWProjectivePointTwisted<F>,
    ) -> Self {
        // Verifying that q is normalized
        let q_is_normalized = q.is_normalized(cs);
        let boolean_true = Boolean::allocated_constant(cs, true);
        Boolean::enforce_equal(cs, &q_is_normalized, &boolean_true);

        // Setting evaluation parameters
        let mut t = q.clone();
        let params = p.x.params.clone();
        let mut f = BN256Fq12NNField::one(cs, &params);

        // Saving Q negative to avoid doing that in the loop
        let mut q_negated = q.negated(cs);

        // Main loop
        for i in (1..SIX_U_PLUS_TWO_WNAF.len()).rev() {
            // Doubling step: f <- f^2 * L_{R,R}(P), T <- 2*T
            // Evaluation of L_{R,R} and 2R is done in the same step
            if i != SIX_U_PLUS_TWO_WNAF.len() - 1 {
                f = f.square(cs);
            }

            let mut doubling = LineFunctionEvaluation::doubling_step(cs, &mut t, p);
            f = Self::mul_f12_by_line_fn(cs, &mut f, &mut doubling);
            t = doubling.point;

            let x = SIX_U_PLUS_TWO_WNAF[i - 1];
            match x {
                1 => {
                    // Addition step: f <- f * L_{T,Q}(P), T <- T + Q
                    let mut addition = LineFunctionEvaluation::addition_step(cs, q, &mut t, p);
                    f = Self::mul_f12_by_line_fn(cs, &mut f, &mut addition);
                    t = addition.point;
                }
                -1 => {
                    // Addition step: f <- f * L_{T,-Q}(P), T <- T - Q
                    let mut addition =
                        LineFunctionEvaluation::addition_step(cs, &mut q_negated, &mut t, p);
                    f = Self::mul_f12_by_line_fn(cs, &mut f, &mut addition);
                    t = addition.point;
                }
                _ => continue,
            }
        }

        // Some additional steps to finalize the Miller loop...
        // Preparing some constants for the Frobenius operator
        let mut q1_mul_factor = Self::allocate_fq2_constant(cs, FROBENIUS_COEFF_FQ6_C1[1], &params);
        let mut q2_mul_factor = Self::allocate_fq2_constant(cs, FROBENIUS_COEFF_FQ6_C1[2], &params);
        let mut xi_to_q_minus_1_over_2 =
            Self::allocate_fq2_constant(cs, XI_TO_Q_MINUS_1_OVER_2, &params);

        // Calculating Frobenius operator Q1 = pi_p(Q)
        let mut q1 = q.clone();
        q1.x = q1.x.conjugate(cs);
        q1.x = q1.x.mul(cs, &mut q1_mul_factor);

        q1.y = q1.y.conjugate(cs);
        q1.y = q1.y.mul(cs, &mut xi_to_q_minus_1_over_2);

        // Calculating Frobenius operator Q2 = -pi_p^2(Q)
        let mut q2 = q.clone();
        q2.x = q2.x.mul(cs, &mut q2_mul_factor);

        // Calculating addition step for T, Q1, f <- f * (line function), T <- T + Q1
        let mut addition = LineFunctionEvaluation::addition_step(cs, &mut q1, &mut t, p);
        f = Self::mul_f12_by_line_fn(cs, &mut f, &mut addition);
        t = addition.point;

        // Calculating addition step for T, -Q2, f <- f * (line function), T <- T - Q2
        let mut addition = LineFunctionEvaluation::addition_step(cs, &mut q2, &mut t, p);
        f = Self::mul_f12_by_line_fn(cs, &mut f, &mut addition);

        Self {
            accumulated_f: f,
            _marker: std::marker::PhantomData::<CS>,
        }
    }

    fn mul_f12_by_line_fn(
        cs: &mut CS,
        f: &mut BN256Fq12NNField<F>,
        line_fn: &mut LineFunctionEvaluation<F, CS>,
    ) -> BN256Fq12NNField<F> {
        let mut f = f.mul_by_c0c3c4(cs, &mut line_fn.c0, &mut line_fn.c3, &mut line_fn.c4);
        f.normalize(cs);
        f
    }

    /// Allocates the constant from `Fq2` constant
    pub fn allocate_fq2_constant(
        cs: &mut CS,
        value: Fq2,
        params: &Arc<BN256BaseNNFieldParams>,
    ) -> BN256Fq2NNField<F> {
        let c0 = BN256BaseNNField::allocated_constant(cs, value.c0, params);
        let c1 = BN256BaseNNField::allocated_constant(cs, value.c1, params);

        BN256Fq2NNField::new(c0, c1)
    }
}

/// Checks the validity of the SWProjective point for the BN256 curve 
/// used in the pairing function. Namely, it verifies that the point is reduced
/// and has a z-coordinate of one (since further the point is represented
/// using Jacobian coordinates)
fn validate_swprojective_point<F, CS>(
    cs: &mut CS,
    point: &mut BN256SWProjectivePoint<F>,
    params: &Arc<BN256BaseNNFieldParams>,
) where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    // Enforcing that the point is reduced
    point.enforce_reduced(cs);

    // Enforcing that the point has a z-coordinate of one
    let mut one = BN256BaseNNField::allocated_constant(cs, BN256Fq::one(), params);
    let mut z = point.z.clone();
    let z_is_one = z.equals(cs, &mut one);
    let boolean_true = Boolean::allocated_constant(cs, true);
    Boolean::enforce_equal(cs, &z_is_one, &boolean_true);
}

/// Checks the validity of the [`BN256SWProjectivePointTwisted`] 
/// used in the pairing function. Namely, it verifies that the point is reduced
/// and has a z-coordinate of one (since further the point is represented
/// using Jacobian coordinates)
fn validate_swprojective_twisted_point<F, CS>(
    cs: &mut CS,
    point: &mut BN256SWProjectivePointTwisted<F>,
    params: &Arc<BN256BaseNNFieldParams>,
) where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    // Enforcing that the point is reduced
    point.enforce_reduced(cs);

    // Enforcing that the point has z-coordinate of one
    let mut one = BN256Fq2NNField::allocated_constant(cs, BN256Fq::one(), params);
    let mut z = point.z.clone();
    let z_is_one = z.equals(cs, &mut one);
    let boolean_true = Boolean::allocated_constant(cs, true);
    Boolean::enforce_equal(cs, &z_is_one, &boolean_true);
}

/// This function computes the pairing function for the BN256 curve using the specified method.
pub fn ec_pairing_inner<F, CS>(
    cs: &mut CS,
    p: &mut BN256SWProjectivePoint<F>,
    q: &mut BN256SWProjectivePointTwisted<F>,
    hardexp_method: HardExpMethod,
    compression_method: CompressionMethod,
) -> BN256Fq12NNField<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    // Validating both points
    let params = &p.x.params.clone();
    validate_swprojective_point(cs, p, params);
    validate_swprojective_twisted_point(cs, q, params);

    // Calculating the Miller Loop and then the final exponentiation
    let mut miller_loop = MillerLoopEvaluation::evaluate(cs, p, q);
    let final_exp = FinalExpEvaluation::evaluate(
        cs,
        &mut miller_loop.accumulated_f,
        hardexp_method,
        compression_method,
    );
    final_exp.resultant_f
}

/// This function computes the pairing function for the BN256 curve using the best method available (that is, the
/// method is chosen under the hood, for more details see [`ec_pairing_inner`])
pub fn ec_pairing<F, CS>(
    cs: &mut CS,
    p: &mut BN256SWProjectivePoint<F>,
    q: &mut BN256SWProjectivePointTwisted<F>,
) -> BN256Fq12NNField<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    ec_pairing_inner(cs, p, q, HardExpMethod::Naive, CompressionMethod::AlgebraicTorus)
}
