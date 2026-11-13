# Formal model (TLA+)

`SwiftNormalisation.tla` is a finite TLA+ model of `Normalisation.scale`, `scaleFrom0To1` and
`scaleFrom0To100` as written in `Sources/SwiftNormalisation`. `Double` is abstracted to **exact
rationals** and inputs to integers in `-Lim..Lim` (`Lim = 3`); every law is checked for all
non-degenerate measure ranges, all scale ranges (including reversed and degenerate ones) and all
inputs, inside and outside the measure range. There is one dummy state (`u = 0`); laws are closed
quantified formulas.

| Invariant | Swift API it abstracts |
|---|---|
| `EndpointsMapToEndpoints` | `scale(minMeasure) == minScale`, `scale(maxMeasure) == maxScale` |
| `InRangeStaysInRange` | doc: result in `minScale...maxScale` for a number inside the measure range |
| `MonotoneWithScaleOrientation` | order preserved (scale range ascending), reversed (descending), constant (degenerate) |
| `DegenerateScaleIsConstant` | `minScale == maxScale` gives that constant |
| `ConstantStep` | linearity: unit step in the input moves the output by `(maxScale-minScale)/(maxMeasure-minMeasure)` |
| `IdentityOnSameRange` | scaling a range onto itself is the identity |
| `InverseRoundTrip` | scaling to another range and applying the swapped formula returns the input |
| `NoClamping` | out-of-range input extrapolates beyond the scale range (no clamping) |
| `From0To1IsScaleTo01`, `From0To1EndpointsAndRange` | `scaleFrom0To1(number:from:to:)` |
| `From0To100IsHundredTimesFrom0To1` | `scaleFrom0To100(number:measureRange:)` (`lowerBound` / `upperBound` map to `0` / `100`) |

## Non-vacuity

`off_by_min` (drops `+ minScale`) -> `EndpointsMapToEndpoints`; `denominator_wrong` (divides by
`maxMeasure`) -> `ConstantStep`; `clamps_result` -> `NoClamping`; `from0to100_uses_99` ->
`From0To100IsHundredTimesFrom0To1`. `run_tlc.sh` fails if a mutant passes.

## Findings

None for the exact-arithmetic semantics. Behaviours outside the model, observed with a throwaway
Swift probe: with `minMeasure == maxMeasure`, `scale` returns `NaN` for `number == minMeasure`
and `+/-inf` otherwise (the doc-comment promises a value in `minScale...maxScale` only for
`number` inside the measure range). 200k random double-precision trials showed
`scale(maxMeasure) == maxScale` exactly and no out-of-range results for in-range inputs, but this
is a sample, not a proof.

## Running

```sh
TLA_JAR=/path/to/tla2tools-1.7.4.jar formal/run_tlc.sh   # needs Java 11+
```

The script checks the jar's SHA-256 against the pinned tla2tools 1.7.4. CI runs it on a
self-hosted Oracle ARM64 runner, only on pushes to the default branch or by manual dispatch
(`.github/workflows/oracle-tla.yml`). The Swift build and tests stay on hosted macOS.

## Limits

Rational arithmetic is not IEEE-754: rounding error, overflow, NaN and infinity are not modelled
(use the Swift tests and snapshots for those). `InverseRoundTrip` applies the inverse formula
directly because the intermediate value is rational. If the Swift formula changes, update the
model in the same PR.
