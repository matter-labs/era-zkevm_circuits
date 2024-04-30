use std::{fs::File, io::Read};

use boojum::{
    cs::traits::cs::ConstraintSystem, ethereum_types::U256, field::goldilocks::GoldilocksField,
    gadgets::u256::UInt256,
};
use lazy_static::lazy_static;
use serde::{Deserialize, Serialize};

type F = GoldilocksField;

/// Path to the test cases
const MODEXP_TEST_CASES_PATH: &str = "./src/modexp/tests_json/modexp_tests.json";
const MODMUL_TEST_CASES_PATH: &str = "./src/modexp/tests_json/modmul_tests.json";

// All tests gathered in one place
lazy_static! {
    /// Test cases for modexp
    pub static ref MODEXP_TEST_CASES: ModexpTestCases = load_modexp_test_cases();
    /// Test cases for modmul
    pub static ref MODMUL_TEST_CASES: ModmulTestCases = load_modmul_test_cases();
}

// --- Modexp Tests ---

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct RawModexpTestCase {
    pub base: String,
    pub exponent: String,
    pub modulus: String,
    pub expected: String,
}

#[derive(Clone, Debug)]
pub struct ModexpTestCase {
    pub base: UInt256<F>,
    pub exponent: UInt256<F>,
    pub modulus: UInt256<F>,
    pub expected: UInt256<F>,
}

impl ModexpTestCase {
    pub fn from_raw<CS>(cs: &mut CS, raw: &RawModexpTestCase) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let base = U256::from_str_radix(raw.base.as_str(), 16).unwrap();
        let exponent = U256::from_str_radix(raw.exponent.as_str(), 16).unwrap();
        let modulus = U256::from_str_radix(raw.modulus.as_str(), 16).unwrap();
        let expected = U256::from_str_radix(raw.expected.as_str(), 16).unwrap();

        ModexpTestCase {
            base: UInt256::allocated_constant(cs, base),
            exponent: UInt256::allocated_constant(cs, exponent),
            modulus: UInt256::allocated_constant(cs, modulus),
            expected: UInt256::allocated_constant(cs, expected),
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct ModexpTestCases {
    pub tests: Vec<RawModexpTestCase>,
}

/// Load modexp test cases from the file
pub(in super::super) fn load_modexp_test_cases() -> ModexpTestCases {
    let mut file = File::open(MODEXP_TEST_CASES_PATH).expect("Unable to open the file");
    let mut data = String::new();
    file.read_to_string(&mut data)
        .expect("Unable to parse to string");
    let test_cases: ModexpTestCases = serde_json::from_str(&data).expect("Failed to deserialize");

    test_cases
}

// --- Modmul Tests ---

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct RawModmulTestCase {
    pub a: String,
    pub b: String,
    pub modulus: String,
    pub expected: String,
}

#[derive(Clone, Debug)]
pub struct ModmulTestCase {
    pub a: UInt256<F>,
    pub b: UInt256<F>,
    pub modulus: UInt256<F>,
    pub expected: UInt256<F>,
}

impl ModmulTestCase {
    pub fn from_raw<CS>(cs: &mut CS, raw: &RawModmulTestCase) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let a = U256::from_str_radix(raw.a.as_str(), 16).unwrap();
        let b = U256::from_str_radix(raw.b.as_str(), 16).unwrap();
        let modulus = U256::from_str_radix(raw.modulus.as_str(), 16).unwrap();
        let expected = U256::from_str_radix(raw.expected.as_str(), 16).unwrap();

        ModmulTestCase {
            a: UInt256::allocated_constant(cs, a),
            b: UInt256::allocated_constant(cs, b),
            modulus: UInt256::allocated_constant(cs, modulus),
            expected: UInt256::allocated_constant(cs, expected),
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct ModmulTestCases {
    pub tests: Vec<RawModmulTestCase>,
}

/// Load modexp test cases from the file
pub(in super::super) fn load_modmul_test_cases() -> ModmulTestCases {
    let mut file = File::open(MODMUL_TEST_CASES_PATH).expect("Unable to open the file");
    let mut data = String::new();
    file.read_to_string(&mut data)
        .expect("Unable to parse to string");
    let test_cases: ModmulTestCases = serde_json::from_str(&data).expect("Failed to deserialize");

    test_cases
}
