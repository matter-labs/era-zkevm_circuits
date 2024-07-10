use ec_pairing::PairingInvalidSubgroupTestCases;
use lazy_static::lazy_static;

use self::{
    algebraic_torus::TorusTestCases,
    ec_add::ECAddTestCases,
    ec_mul::{DecompositionTestCases, MultiplicationTestCases},
    ec_pairing::{FinalExpTestCases, G2TestCases, LineFunctionTestCases, PairingTestCases},
    field_extensions::{Fq12TestCases, Fq2TestCases, Fq6TestCases},
};

pub mod algebraic_torus;
pub mod ec_add;
pub mod ec_mul;
pub mod ec_pairing;
pub mod field_extensions;
pub mod types;

// All tests gathered in one place
lazy_static! {
    /// Test cases for EC addition
    pub static ref EC_ADD_TEST_CASES: ECAddTestCases = ec_add::load_ec_add_test_cases();
    /// Test cases for scalar decomposition
    pub static ref DECOMPOSITION_TEST_CASES: DecompositionTestCases = ec_mul::load_decomposition_test_cases();
    /// Test cases for scalar multiplication
    pub static ref EC_MUL_TEST_CASES: MultiplicationTestCases = ec_mul::load_multiplication_test_cases();
    /// Test cases for `Fq2` operations
    pub static ref FQ2_TEST_CASES: Fq2TestCases = field_extensions::load_fq2_test_cases();
    /// Test cases for `Fq6` operations
    pub static ref FQ6_TEST_CASES: Fq6TestCases = field_extensions::load_fq6_test_cases();
    /// Test cases for `Fq12` operations
    pub static ref FQ12_TEST_CASES: Fq12TestCases = field_extensions::load_fq12_test_cases();
    /// Test cases for `G2` operations
    pub static ref G2_CURVE_TEST_CASES: G2TestCases = ec_pairing::load_g2_curve_test_cases();
    /// Test cases for Line function operations
    pub static ref LINE_FUNCTION_TEST_CASES: LineFunctionTestCases = ec_pairing::load_line_function_test_cases();
    /// Test cases for easy exponentiation
    pub static ref FINAL_EXP_TEST_CASES: FinalExpTestCases = ec_pairing::load_final_exp_test_cases();
    /// Test cases for pairing bilinearity
    pub static ref PAIRING_TEST_CASES: PairingTestCases = ec_pairing::load_pairing_test_cases();
    /// Test cases for pairing invalid subgroup checks
    pub static ref INVALID_SUBGROUP_TEST_CASES: PairingInvalidSubgroupTestCases = ec_pairing::load_pairing_invalid_subgroup_test_cases();
    /// Test cases for algebraic torus operations
    pub static ref TORUS_TEST_CASES: TorusTestCases = algebraic_torus::load_torus_test_cases();
}
