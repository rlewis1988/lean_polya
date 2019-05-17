import .term .tactic

open tactic polya.term polya.tactic

constants x y z : ℝ

meta def test (e : expr) : tactic unit :=
do
    (t, hyp) ← term_of_expr e,
    ((), pr) ← solve_aux hyp `[refl; done],
    infer_type pr >>= trace

set_option trace.app_builder true
run_cmd test `(x*y + z*1 + y*0)
