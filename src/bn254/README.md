# BN254 Elliptic Curve Circuits

This folder contains circuits for elliptic curve operations over the BN254 curve. Namely,
we implement the following three precompiles:

- `ecmul` - Elliptic curve point multiplication.
- `ecadd` - Elliptic curve point addition.
- `ecpairing` - Elliptic curve pairing.

## :file_folder: Structure

The package is structured as follows:

| Path | Description |
| --- | --- |
| [`ec_add`](ec_add) | Circuit for elliptic curve point addition. |
| [`ec_mul`](ec_mul) | Circuit for elliptic curve point multiplication. |
| [`ec_pairing`](ec_pairing) | Circuit for elliptic curve pairing. |
| [`sage`](sage) | Sage code for debugging and experimenting. |
| [`tests`](tests) | Tests for the circuits which checks their validity. |

## :zap: Performance

The circuits are optimized for performance. Below, we list
the number of constraints for each circuit.

| Circuit | General Purpose Rows |
| --- | --- |
| `ec_add` | 260 |
| `ec_mul` | 40,055 |
| `miller_loop` | 195,961 |
| `final_exp_no_torus` | 414,158 |
| `final_exp_divigili` | 421,586 |
| `ec_pairing_naive` | 610,004 |

## :spiral_notepad: Precompile Final Performance

| Circuit | General Purpose Rows |
| --- | --- |
| `ec_add` | 260 |
| `ec_mul` | 40,055 |
| `ec_pairing` | 610,004 |
| `modexp` (_32-4-32_ version) | 160,827 |
