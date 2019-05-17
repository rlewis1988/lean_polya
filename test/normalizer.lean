import normalizer

open polya

constants a b c u v w z y x: ℚ

private meta def test_on (e : expr) := (do
    t ← expr.to_term e,
    st ← term.canonize t,
    tactic.trace st
)

run_cmd test_on `(1*a + 3*(b + c) + 5*b)
run_cmd test_on `((1*u + (2* (1* v ^ 2 + 23*1) ^ 3) + 1*z) ^ 3)
