# Modexp Precompile Circuits

This folder contains circuits for the `modexp` precompile. Namely,
we implement the operation $b^e$ mod $m$. Since we are limited
by the size of each integer, we include different versions of the
circuit to handle different sizes $b,e,m$. The circuits are:

- 32-32-32: $b,e,m$ are 32-byte integers.
- 32-4-32: $b,m$ are 32-byte integers, $e$ is a 4-byte integer.
- 256-256-256: $b,e,m$ are 256-byte integers.
- 256-8-256: $b,m$ are 256-byte integers, $e$ is a 8-byte integer.

## :file_folder: Structure

The package is structured as follows:

| Path | Description |
| --- | --- |
| [`implementation`](implementation) | Main circuits. |
| [`tests_json`](tests_json) | JSON files with tests. |
| [`test.rs`](test.rs) | File with `modexp` tests. |
| [`input.rs`](input.rs) | Entrypoints for further integration. |

## :zap: Performance

The circuits are optimized for performance. Below, we list
the number of constraints for each circuit.

| Circuit | General Purpose Rows |
| --- | --- |
| 32-32 `modmul` | 2,527 |
| 32-4-32 `modexp` | 160,827 |
| 32-32-32 `modexp` | ~1,286,616 |
| 256-256 `modmul` | Untested |
| `modexp`, 256-byte $b,m$ | Untested |
