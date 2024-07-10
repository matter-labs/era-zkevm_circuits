use super::types::{RawFq12, RawFq6};
use serde::{Deserialize, Serialize};

/// Path to the test cases for Torus operations
const TORUS_TEST_CASES: &str = include_str!("torus_tests.json");

// --- Torus tests ---

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct TorusTestCase {
    pub scalar_1: RawFq12,
    pub scalar_2: RawFq12,
    pub expected: TorusExpectedValue,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct TorusExpectedValue {
    pub encoding_1: RawFq6,
    pub encoding_2: RawFq6,
    pub product_encoding: RawFq6,
    pub inverse_1_encoding: RawFq6,
    pub conjugate_1_encoding: RawFq6,
    pub square_1_encoding: RawFq6,
    pub frobenius_1_encoding: RawFq6,
    pub frobenius_2_encoding: RawFq6,
    pub frobenius_3_encoding: RawFq6,
    pub power_u_encoding: RawFq6,
    pub power_13_encoding: RawFq6,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct TorusTestCases {
    pub tests: Vec<TorusTestCase>,
}

/// Load EC addition test cases from the file
pub(in super::super) fn load_torus_test_cases() -> TorusTestCases {
    serde_json::from_str(&TORUS_TEST_CASES).expect("Failed to deserialize")
}
