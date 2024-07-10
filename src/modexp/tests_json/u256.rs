use boojum::{
    cs::traits::cs::ConstraintSystem,
    ethereum_types::U256,
    field::goldilocks::GoldilocksField,
    gadgets::{u256::UInt256, u32::UInt32},
};
use serde::{Deserialize, Serialize};

type F = GoldilocksField;

/// Path to the test cases
const MODEXP_32_32_32_TEST_CASES_STR: &str = include_str!("modexp_32-32-32_tests.json");
const MODEXP_32_4_32_TEST_CASES_STR: &str = include_str!("modexp_32-4-32_tests.json");
const MODMUL_32_32_TEST_CASES_STR: &str = include_str!("modmul_32-32_tests.json");

// --- Modexp Tests ---
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct RawModexp32BytesTestCase {
    pub base: String,
    pub exponent: String,
    pub modulus: String,
    pub expected: String,
}

#[derive(Clone, Debug)]
pub struct Modexp32BytesLargeExpTestCase {
    pub base: UInt256<F>,
    pub exponent: UInt256<F>,
    pub modulus: UInt256<F>,
    pub expected: UInt256<F>,
}

impl Modexp32BytesLargeExpTestCase {
    pub fn from_raw<CS>(cs: &mut CS, raw: &RawModexp32BytesTestCase) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let base = U256::from_str_radix(raw.base.as_str(), 16).unwrap();
        let exponent = U256::from_str_radix(raw.exponent.as_str(), 16).unwrap();
        let modulus = U256::from_str_radix(raw.modulus.as_str(), 16).unwrap();
        let expected = U256::from_str_radix(raw.expected.as_str(), 16).unwrap();

        Self {
            base: UInt256::allocated_constant(cs, base),
            exponent: UInt256::allocated_constant(cs, exponent),
            modulus: UInt256::allocated_constant(cs, modulus),
            expected: UInt256::allocated_constant(cs, expected),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Modexp32BytesSmallExpTestCase {
    pub base: UInt256<F>,
    pub exponent: UInt32<F>,
    pub modulus: UInt256<F>,
    pub expected: UInt256<F>,
}

impl Modexp32BytesSmallExpTestCase {
    pub fn from_raw<CS>(cs: &mut CS, raw: &RawModexp32BytesTestCase) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let base = U256::from_str_radix(raw.base.as_str(), 16).unwrap();
        let exponent = u32::from_str_radix(raw.exponent.as_str(), 16).unwrap();
        let modulus = U256::from_str_radix(raw.modulus.as_str(), 16).unwrap();
        let expected = U256::from_str_radix(raw.expected.as_str(), 16).unwrap();

        Self {
            base: UInt256::allocated_constant(cs, base),
            exponent: UInt32::allocated_constant(cs, exponent),
            modulus: UInt256::allocated_constant(cs, modulus),
            expected: UInt256::allocated_constant(cs, expected),
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Modexp32BytesTestCases {
    pub tests: Vec<RawModexp32BytesTestCase>,
}

/// Load 32-32-32 modexp test cases from the file
pub(in super::super) fn load_modexp_32_32_32_test_cases() -> Modexp32BytesTestCases {
    serde_json::from_str(MODEXP_32_32_32_TEST_CASES_STR).expect("Failed to deserialize")
}

/// Load 32-4-32 modexp test cases from the file
pub(in super::super) fn load_modexp_32_4_32_test_cases() -> Modexp32BytesTestCases {
    serde_json::from_str(MODEXP_32_4_32_TEST_CASES_STR).expect("Failed to deserialize")
}

// --- Modmul Tests ---

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct RawModmul32BytesTestCase {
    pub a: String,
    pub b: String,
    pub modulus: String,
    pub expected: String,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Modmul32BytesTestCases {
    pub tests: Vec<RawModmul32BytesTestCase>,
}

#[derive(Clone, Debug)]
pub struct Modmul32BytesTestCase {
    pub a: UInt256<F>,
    pub b: UInt256<F>,
    pub modulus: UInt256<F>,
    pub expected: UInt256<F>,
}

impl Modmul32BytesTestCase {
    pub fn from_raw<CS>(cs: &mut CS, raw: &RawModmul32BytesTestCase) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let a = U256::from_str_radix(raw.a.as_str(), 16).unwrap();
        let b = U256::from_str_radix(raw.b.as_str(), 16).unwrap();
        let modulus = U256::from_str_radix(raw.modulus.as_str(), 16).unwrap();
        let expected = U256::from_str_radix(raw.expected.as_str(), 16).unwrap();

        Modmul32BytesTestCase {
            a: UInt256::allocated_constant(cs, a),
            b: UInt256::allocated_constant(cs, b),
            modulus: UInt256::allocated_constant(cs, modulus),
            expected: UInt256::allocated_constant(cs, expected),
        }
    }
}

/// Load 32-byte modexp test cases from the file
pub(in super::super) fn load_modmul_32_32_test_cases() -> Modmul32BytesTestCases {
    serde_json::from_str(MODMUL_32_32_TEST_CASES_STR).expect("Failed to deserialize")
}
