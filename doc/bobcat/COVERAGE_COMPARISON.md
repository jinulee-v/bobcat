# BOBCat coverage comparison

This document records the retained goal-driven BOBCat campaign completed on
September 15, 2026. It is a result report, not an ablation study.

## Configuration

- 23 public wrapper scopes across five datasets
- 1,800-second outer timeout per wrapper
- demand-driven compilation
- maximum input-list length 5
- intermediate-list storage bound 5
- ordinary SAT queries (`--bobcat-maxsat-timeout-ms=0`)
- coverage credited only after successful complete native replay

MaxSAT was **not** used in the retained run. Results from optional eager or
MaxSAT strategies are not combined with these numbers.

## Source branch outcomes

| Dataset | Supplied original baseline | Previous local recovery | Retained BOBCat | Change from original |
|---|---:|---:|---:|---:|
| SARA | 130/425 | 6/425 | 116/425 | -14 |
| Airline | 226/278 | 243/278 | 243/278 | +17 |
| Logement | 1002/4706 | 229/4706 | 1479/4706 | +477 |
| Familiales | 12/214 | 109/214 | 113/214 | +101 |
| NSW community gaming | 14/14 | 14/14 | 14/14 | 0 |
| **Total** | **1384/5637** | **601/5637** | **1965/5637** | **+581** |

The aggregate increase over the supplied baseline is 581 outcomes, about
42.0%. The supplied baseline was not rerun from an archived original binary,
so the table should not be interpreted as a controlled per-optimization
experiment.

The retained dataset contains 402 validated test cases: 25 for SARA, 111 for
Airline, 181 for Logement, 54 for Familiales, and 31 for NSW community gaming.
One test may cover many source outcomes, and outcomes observed incidentally
during a successful replay are credited.

## Runtime and remaining failures

| Dataset | Previous wrapper seconds (sum) | Retained wrapper seconds (sum) | Previous timeouts | Retained timeouts |
|---|---:|---:|---:|---:|
| SARA | 14035.0 | 13316.0 | 7/9 | 6/9 |
| Airline | 407.6 | 1032.1 | 0/1 | 0/1 |
| Logement | 3605.6 | 1680.4 | 2/4 | 0/4 |
| Familiales | 1819.8 | 557.0 | 1/2 | 0/2 |
| NSW community gaming | 2.1 | 5.6 | 0/7 | 0/7 |

Wrapper seconds are summed process wall times; wrappers ran concurrently. Six
wrappers timed out. TaxableIncome, HousingAid, and FamilyAllowance reported Z3
`max. memory exceeded`. UnemploymentTax exited on SIGKILL, whose cause was not
established by its log. Early error exits are not performance improvements.
Airline reached the same 243 outcomes as the previous recovery run but took
longer.

The explicit intermediate storage bound is an additional search restriction.
Consequently, unsuccessful searches in this configuration cannot certify
infeasibility over the complete input-list-bounded domain. Replay-validated
witnesses remain valid executions of the original program.

## Retained design

The retained implementation combines:

- demand-driven goal slices and lazy semantic relations;
- failure-directed assertion, fatal-error, and missing-rule refinement;
- fresh solver sessions per goal, with reuse inside each goal;
- refinement before increasing a timed-out replay budget;
- fixed-point analysis of function-containing type declarations; and
- guarded definition and reachability sharing.

The measured campaign used a separately built Z3 4.13.3 with per-model
memoization of function-interpretation eligibility. That build is maintained by
the surrounding benchmark harness, rather than this compiler repository.

The retained compiler binary passed 59 harness regression tests. The exact
campaign depends on public wrappers, the isolated Z3 build, and measurement
scripts in the surrounding `formalization_rtf` workspace. For auditability, it
recorded these immutable hashes:

- compiler: `99c535537d908fe3dbfecd1af6bb9362da7aaaa10995beded6bb40515b061106`
- Z3 library: `068d5dc2e71f344ba0338673c798f5ba65fdcd8403e886f6bf8c023ca28d607f`

Dataset coverage must be computed as the union of exact outcomes from successful
replay traces; objective SAT counts are not a substitute for source coverage.
