use lazy_static::lazy_static;

pub mod u2048;
pub mod u256;

// All tests gathered in one place
lazy_static! {
    /// Test cases for 32-32-32 modexp
    pub static ref MODEXP_32_32_32_TEST_CASES: u256::Modexp32BytesTestCases = u256::load_modexp_32_32_32_test_cases();
    /// Test cases for 32-4-32 modexp
    pub static ref MODEXP_32_4_32_TEST_CASES: u256::Modexp32BytesTestCases = u256::load_modexp_32_4_32_test_cases();
    /// Test cases for modmul
    pub static ref MODMUL_32_32_TEST_CASES: u256::Modmul32BytesTestCases = u256::load_modmul_32_32_test_cases();
    /// Test cases for modmul
    pub static ref MODMUL_256_256_TEST_CASES: u2048::Modmul256BytesTestCases = u2048::load_modmul_256_256_test_cases();
}
