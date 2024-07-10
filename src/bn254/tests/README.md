# :test_tube: Elliptic Curve Tests

This folder contains tests for EC operations: `ecmul`, `ecadd`, and `ecpairing`,
and related entities:

- Tower extension fields: `fp2`, `fp6`, `fp12`.
- Pairing-friendly curves: `bn254` and `G2` twisted curve.

## :file_folder: Structure

The package is structured as follows:

| Path | Description |
| --- | --- |
| This folder | Tests themselves. |
| [`sage`](./sage) | Sage code for generating tests. |
| [`json`](./json) | JSON files with test values (inputs and expected values). |
