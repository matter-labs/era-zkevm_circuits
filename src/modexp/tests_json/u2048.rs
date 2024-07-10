use boojum::{
    crypto_bigint::U1024, cs::traits::cs::ConstraintSystem, field::goldilocks::GoldilocksField,
    gadgets::u2048::UInt2048,
};
use serde::{Deserialize, Serialize};

type F = GoldilocksField;

/// Path to the test cases
const MODMUL_256_256_TEST_CASES_STR: &str = include_str!("modmul_256-256_tests.json");

// --- Modmul Tests ---
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct RawU2048 {
    pub low: String,
    pub high: String,
}

impl RawU2048 {
    pub fn to_u2048<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> UInt2048<F> {
        let low = U1024::from_le_hex(&self.low);
        let high = U1024::from_le_hex(&self.high);

        UInt2048::allocated_constant(cs, (low, high))
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct RawModmul256BytesTestCase {
    pub a: RawU2048,
    pub b: RawU2048,
    pub modulus: RawU2048,
    pub expected: RawU2048,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Modmul256BytesTestCases {
    pub tests: Vec<RawModmul256BytesTestCase>,
}

#[derive(Clone, Debug)]
pub struct Modmul256BytesTestCase {
    pub a: UInt2048<F>,
    pub b: UInt2048<F>,
    pub modulus: UInt2048<F>,
    pub expected: UInt2048<F>,
}

impl Modmul256BytesTestCase {
    pub fn from_raw<CS>(cs: &mut CS, raw: &RawModmul256BytesTestCase) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        Modmul256BytesTestCase {
            a: raw.a.to_u2048(cs),
            b: raw.b.to_u2048(cs),
            modulus: raw.modulus.to_u2048(cs),
            expected: raw.expected.to_u2048(cs),
        }
    }
}

/// Load 32-byte modexp test cases from the file
pub(in super::super) fn load_modmul_256_256_test_cases() -> Modmul256BytesTestCases {
    serde_json::from_str(MODMUL_256_256_TEST_CASES_STR).expect("Failed to deserialize")
}
