import normalizer

open polya polya.canonize field tactic.field tactic

constants a b c u v w z y x : ℝ

private meta def test_on (e : expr) : tactic unit := (do
  let (t, s) := (eterm_of_expr e).run ∅,
  new_e ← nterm_to_expr `(ℝ) s (norm t),
  trace new_e
)

run_cmd test_on `(((1 : ℚ) : ℝ) * a + (3 : ℚ) * (b + c) + (5 : ℚ) * b)
run_cmd test_on `((((1 : ℚ) : ℝ) * u + ((2 : ℚ) * ((1 : ℚ) * v ^ 2 + (23 : ℚ) * 1) ^ 3) + 1 * z) ^ 3)

constant h1 : x * (1 / 10 : ℚ) + x * (1 / 10 : ℚ) - x * (1 / 5 : ℚ) ≤ y

run_cmd (do
  e ← to_expr ``(h1),
  (mv, l, pr) ← canonize_hyp e,

  --gs ← get_goals,
  --set_goals [mv],
  --reflexivity,
  --set_goals gs,
  
  infer_type mv >>= trace,
  trace "",
  infer_type pr >>= trace,
  trace "",
  monad.mapm (λ x, infer_type x >>= trace >> trace "") l
)


