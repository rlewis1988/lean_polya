import .tactic

open tactic polya

set_option trace.check true
meta def test (e : expr) : tactic unit :=
do
    (naive_new_e, new_e, hyps) ← test_norm e,
    trace naive_new_e,
    trace new_e,
    trace hyps,
    skip

constants u v w x y z : ℝ

/- benchmak -/
set_option profiler true

/- debug -/
--set_option trace.app_builder true

--sterm tests
run_cmd test `( x - x )
run_cmd test `( x * (1 / 10 : ℚ) + x * (1 / 10 : ℚ) - x * (1 / 5 : ℚ))
run_cmd test `( x * (3 : ℚ) + y * (1 : ℚ) - x * y * (2 : ℚ) - y * (2 : ℚ) )
run_cmd test `( x * y * z * (3 : ℚ) - z * x * y * (4 : ℚ) )

--pterm tests
run_cmd test `( x * ((y * w) * (z * (u * z) * v) * w) )
run_cmd test `( (x * (2 : ℚ)) * ((3 : ℚ) / x) )
run_cmd test `( (x * y) ^ 3 / x ^ 2 )
run_cmd test `( (x - y + y) * z )
run_cmd test `( (x / x) ^ 0 )
run_cmd test `( (x + y) ^ 2 / (x + y) ^ 2 * x * y / x )
run_cmd test `( x ^ 4 )

