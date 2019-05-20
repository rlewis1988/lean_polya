import .term .tactic

open tactic polya polya.term

-- build term and proove equality
meta def test (e : expr) : tactic unit :=
do
    (_, pr) ← nterm_of_expr e,
    infer_type pr >>= trace

constants x y z : ℝ

/- benchmak -/
set_option profiler true

run_cmd test `(x * y + 1 * x + 0 * (z + y))
run_cmd test `(x * 2)
run_cmd test `(x * (2 : γ))
