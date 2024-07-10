use serde::{Deserialize, Serialize};

use crate::bn254::tests::json::types::{RawFq12, RawFq2, RawFq6};

/// Path to the test cases for Fq2 operations
const FQ2_TEST_CASES: &str = include_str!("fq2_tests.json");
/// Path to the test cases for Fq6 operations
const FQ6_TEST_CASES: &str = include_str!("fq6_tests.json");
/// Path to the test cases for Fq6 operations
const FQ12_TEST_CASES: &str = include_str!("fq12_tests.json");

// --- Fq2 tests ---

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Fq2TestCase {
    pub scalar_1: RawFq2,
    pub scalar_2: RawFq2,
    pub expected: Fq2ExpectedValue,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Fq2ExpectedValue {
    pub sum: RawFq2,
    pub difference: RawFq2,
    pub product: RawFq2,
    pub quotient: RawFq2,
    pub scalar_1_non_residue: RawFq2,
    pub frobenius_6: RawFq2,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Fq2TestCases {
    pub tests: Vec<Fq2TestCase>,
}

/// Load Fq2 test cases from the file
pub(in super::super) fn load_fq2_test_cases() -> Fq2TestCases {
    serde_json::from_str(&FQ2_TEST_CASES).expect("Failed to deserialize")
}

// --- Fq6 Test Cases ---

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Fq6TestCase {
    pub scalar_1: RawFq6,
    pub scalar_2: RawFq6,
    pub c0: RawFq2,
    pub c1: RawFq2,
    pub c2: RawFq2,
    pub expected: Fq6ExpectedValue,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Fq6ExpectedValue {
    pub sum: RawFq6,
    pub difference: RawFq6,
    pub product: RawFq6,
    pub quotient: RawFq6,
    pub product_c1: RawFq6,
    pub product_c0c1: RawFq6,
    pub product_c2: RawFq6,
    pub scalar_1_inverse: RawFq6,
    pub scalar_1_square: RawFq6,
    pub scalar_1_non_residue: RawFq6,
    pub scalar_1_frobenius_1: RawFq6,
    pub scalar_2_frobenius_2: RawFq6,
    pub scalar_1_frobenius_3: RawFq6,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Fq6TestCases {
    pub tests: Vec<Fq6TestCase>,
}

/// Load `Fq6` test cases from the file
pub(in super::super) fn load_fq6_test_cases() -> Fq6TestCases {
    serde_json::from_str(&FQ6_TEST_CASES).expect("Failed to deserialize")
}

// --- Fq12 Test Cases ---

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Fq12TestCase {
    pub scalar_1: RawFq12,
    pub scalar_2: RawFq12,
    pub c0: RawFq2,
    pub c1: RawFq2,
    pub c3: RawFq2,
    pub c4: RawFq2,
    pub c5: RawFq2,
    pub expected: Fq12ExpectedValue,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Fq12ExpectedValue {
    pub sum: RawFq12,
    pub difference: RawFq12,
    pub product: RawFq12,
    pub quotient: RawFq12,
    pub scalar_1_inverse: RawFq12,
    pub scalar_1_square: RawFq12,
    pub product_c0c3c4: RawFq12,
    pub product_c0c1c4: RawFq12,
    pub product_c5: RawFq12,
    pub scalar_1_frobenius_1: RawFq12,
    pub scalar_2_frobenius_2: RawFq12,
    pub scalar_1_frobenius_3: RawFq12,
    pub scalar_1_pow_33: RawFq12,
    pub scalar_2_pow_67: RawFq12,
    pub scalar_1_pow_u: RawFq12,
    pub scalar_1_pow_u2: RawFq12,
    pub scalar_1_pow_u3: RawFq12,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Fq12TestCases {
    pub tests: Vec<Fq12TestCase>,
}

/// Load `Fq12` test cases from the file
pub(in super::super) fn load_fq12_test_cases() -> Fq12TestCases {
    serde_json::from_str(&FQ12_TEST_CASES).expect("Failed to deserialize")
}
