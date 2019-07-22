import normalizer

open polya field tactic.polya.field tactic

constants a b c u v w z y x : α

example (h1 : x * (1 / 2) + x * (1 / 2) - x ≤ y) : y ≥ 0 :=
by do
  e ← get_local `h1,
  (mv, l, pr) ← canonize_hyp e,
  prove_by_reflexivity [mv],
  exact pr

