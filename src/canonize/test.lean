import .tactic
import .pterm

open tactic polya

meta def test (e : expr) : tactic unit :=
do
    (nt, ρ, pr) ← nterm_of_expr e,
    nt ← eval_expr (@nterm γ _) nt,
    type_check pr,
    trace nt,
    skip

meta def ptest (e : expr) : tactic unit :=
do
    (nt, ρ, pr) ← nterm_of_expr e,
    nt ← eval_expr (@nterm γ _) nt,
    type_check pr,

    let pt := pterm.of_nterm nt,
    trace "term from the expression:",
    trace nt,
    trace "semi-normalized form:",
    trace pt.filter.to_nterm,
    trace "under the condition that these are non zero:",
    trace pt.filter_hyps,
    skip

constants x y z : ℝ

/- benchmak -/
set_option profiler true

/- debug -/
set_option trace.app_builder true

--sterm tests
run_cmd test `( x - x )
run_cmd test `( x * (1 / 10 : ℚ) + x * (1 / 10 : ℚ) - x * (1 / 5 : ℚ))
run_cmd test `( x * (3 : ℚ) + y * (1 : ℚ) - x * y * (2 : ℚ) - y * (2 : ℚ) )
run_cmd test `( x * y * (3 : ℚ) - x * y * (4 : ℚ) )

--pterm tests
run_cmd ptest `( x * x)
run_cmd ptest `( x / x )
run_cmd ptest `( x ^ 2 / x ^ 2 )
run_cmd ptest `( (x * (2 : ℚ)) * ((3 : ℚ) / x) )
run_cmd ptest `( (x * y) ^ 3 / x ^ 2 )
run_cmd ptest `( x * x * x * y * x * x / y)
run_cmd ptest `( (x + y) ^ 2 / (x + y) ^ 2 * x )
