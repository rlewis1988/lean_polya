import .term .tactic

open tactic polya polya.term

meta def test (e : expr) : tactic unit :=
do
    (t, ρ, pr) ← nterm_of_expr e,
    trace t,
    type_check pr,
    pr ← infer_type pr,
    hyp ← to_expr ``(%%e = nterm.eval %%ρ %%(reflect t)),
    if pr = hyp then trace "ok" else failure,
    skip

constants x y z : ℝ

/- benchmak -/
set_option profiler true

/- debug -/
set_option trace.app_builder true

run_cmd test `(x * y + 1 * x + 0 * (z + y))
run_cmd test `(x / x)
run_cmd test `(x ^ 4)
run_cmd test `(x * 2)
run_cmd test `(x * (2 : γ))
run_cmd test `( x * (0.1 : ℚ) + x * (0.1 : ℚ) - x * (0.2 : ℚ) )

#check (rfl : rat.mk 1 10 + rat.mk 1 10 - rat.mk 1 5 = 0)
