import .datatypes -- blackboard

namespace polya

--@[reducible] def α := ℚ
--@[reducible] def γ := ℚ

namespace gen_comp

--def to_rel : gen_comp → ℝ → ℝ → Prop
--| le := (≤)
--| lt := (<)
--| ge := (≥)
--| gt := (>)
--| eq := (=)
--| ne := (≠)

section
variables {u v x y a : ℚ} --TODO: more general hypothesis?

lemma lemma_pos_le (h1 : u - v = (x - y) * a) : a > 0 → u ≤ v → x ≤ y :=
begin
  intros h2 h3,
  apply le_of_sub_nonneg,
  apply nonneg_of_neg_nonpos,
  apply le_of_mul_le_mul_right _ h2,
  rw [zero_mul, neg_sub, ← h1],
  apply sub_nonpos_of_le,
  apply h3
end
lemma lemma_pos_lt (h1 : u - v = (x - y) * a) : a > 0 → u < v → x < y :=
begin
  intros h2 h3,
  apply lt_of_sub_neg,
  apply neg_of_neg_pos,
  apply lt_of_mul_lt_mul_right _ (le_of_lt h2),
  rw [zero_mul, neg_mul_eq_neg_mul_symm, ← h1],
  apply neg_pos_of_neg,
  apply sub_neg_of_lt,
  apply h3
end
lemma lemma_pos_ge (h1 : u - v = (x - y) * a) : a > 0 → u ≥ v → x ≥ y :=
begin
  apply lemma_pos_le,
  apply eq_of_neg_eq_neg,
  rw [← neg_mul_eq_neg_mul_symm, neg_sub, neg_sub],
  apply h1
end
lemma lemma_pos_gt (h1 : u - v = (x - y) * a) : a > 0 → u > v → x > y :=
begin
  apply lemma_pos_lt,
  apply eq_of_neg_eq_neg,
  rw [← neg_mul_eq_neg_mul_symm, neg_sub, neg_sub],
  apply h1
end
lemma lemma_pos_eq (h1 : u - v = (x - y) * a) : a > 0 → u = v → x = y :=
begin
  intros h2 h3,
  apply eq_of_sub_eq_zero,
  have : a ≠ 0, from ne_of_gt h2,
  apply eq_of_mul_eq_mul_right this, 
  apply eq.symm,
  rw [zero_mul, ← sub_eq_zero.mpr h3],
  apply h1
end
lemma lemma_pos_ne (h1 : u - v = (x - y) * a) : a > 0 → u ≠ v → x ≠ y :=
begin
  intros h2 h3,
  intro h4, apply h3,
  apply eq_of_sub_eq_zero,
  rw h1,
  apply mul_eq_zero.mpr,
  left,
  apply sub_eq_zero_of_eq,
  apply h4
end

lemma aux : u - v = (x - y) * a → u - v = (y - x) * (-a) :=
begin
  intro h,
  rw mul_neg_eq_neg_mul_symm,
  rw neg_mul_eq_neg_mul,
  rw neg_sub,
  apply h
end

lemma lemma_neg_le (h1 : u - v = (x - y) * a) : a < 0 → u ≤ v → x ≥ y :=
λ h2 h3, lemma_pos_le (aux h1) (neg_pos_of_neg h2) h3
lemma lemma_neg_lt (h1 : u - v = (x - y) * a) : a < 0 → u < v → x > y :=
λ h2 h3, lemma_pos_lt (aux h1) (neg_pos_of_neg h2) h3
lemma lemma_neg_ge (h1 : u - v = (x - y) * a) : a < 0 → u ≥ v → x ≤ y :=
λ h2 h3, lemma_pos_ge (aux h1) (neg_pos_of_neg h2) h3
lemma lemma_neg_gt (h1 : u - v = (x - y) * a) : a < 0 → u > v → x < y :=
λ h2 h3, lemma_pos_gt (aux h1) (neg_pos_of_neg h2) h3
lemma lemma_neg_eq (h1 : u - v = (x - y) * a) : a < 0 → u = v → x = y :=
λ h2 h3, eq.symm $ lemma_pos_eq (aux h1) (neg_pos_of_neg h2) h3
lemma lemma_neg_ne (h1 : u - v = (x - y) * a) : a < 0 → u ≠ v → x ≠ y :=
λ h2 h3, ne.symm $ lemma_pos_ne (aux h1) (neg_pos_of_neg h2) h3

end

open tactic

meta def canonize (op : gen_comp) (a : ℚ) (pr1 pr2 : expr) : tactic expr :=
do
  -- a should not be equal to 0
  let h3 : expr := if a > 0 then `((%%(reflect a) : ℚ) > 0) else `((%%(reflect a) : ℚ) < 0),
  pr3 ← mk_meta_var h3,

  dec ← mk_instance `(decidable %%h3),
  mk_app ``is_true [pr3] >>= unify dec,

  let decl : name := match op with
  | le := if a > 0 then ``lemma_pos_le else ``lemma_neg_le 
  | lt := if a > 0 then ``lemma_pos_lt else ``lemma_neg_lt
  | ge := if a > 0 then ``lemma_pos_ge else ``lemma_neg_ge
  | gt := if a > 0 then ``lemma_pos_gt else ``lemma_neg_gt
  | eq := if a > 0 then ``lemma_pos_eq else ``lemma_neg_eq
  | ne := if a > 0 then ``lemma_pos_ne else ``lemma_neg_ne
  end,
  foo ← resolve_name decl,
  e ← to_expr ``(%%foo %%pr1 %%pr3 %%pr2) tt ff,
  --e ← mk_app decl [pr1, pr3, pr2],
  return e

end gen_comp

open tactic field polya.field tactic.polya.field

meta def prove_inequality (lhs rhs pf : expr) (op : gen_comp) :
  tactic (expr × list expr × expr) :=
do
  (t1, s) ← (term_of_expr lhs).run ∅,
  (t2, s) ← (term_of_expr rhs).run s,
  ρ ← s.dict_expr `(α),

  (mvars1, h_aux_1) ← prove_norm_hyps t1 s,
  (mvars2, h_aux_2) ← prove_norm_hyps t2 s,

  let (t1', t2', c) := norm2 γ t1 t2,
  trace t1',
  lhs' ← nterm_to_expr s t1',
  rhs' ← nterm_to_expr s t2',
  let c_expr : expr := reflect c,
  let op' := if c > 0 then op else op.reverse,

  h_aux_3 ← to_expr ``((%%(reflect t1'), %%(reflect t2'), %%(c_expr)) = norm2 γ %%(reflect t1) %%(reflect t2))
    >>= mk_meta_var,
  
  e1 ← to_expr ``(%%lhs - %%rhs),
  e2 ← to_expr ``(term.eval %%ρ %%(reflect t1) - term.eval %%ρ %%(reflect t2)),
  e3 ← to_expr ``((nterm.eval %%ρ %%(reflect t1') - nterm.eval %%ρ %%(reflect t2')) * ↑%%(c_expr)),
  e4 ← to_expr ``((%%lhs' - %%rhs') * ↑%%(c_expr)),

  h1 ← to_expr ``(%%e1 = %%e2),
  ((), pr1) ← solve_aux h1 `[refl, done],
  pr2 ← to_expr ``(eval_norm2 %%h_aux_1 %%h_aux_2 %%h_aux_3) tt ff,
  h3 ← to_expr ``(%%e3 = %%e4),
  ((), pr3) ← solve_aux h3 `[refl, done],
  pr ← mk_eq_trans pr2 pr3 >>= mk_eq_trans pr1,
  pr ← gen_comp.canonize op c pr pf,

  return (h_aux_3, mvars1 ++ mvars2, pr)

meta def canonize_hyp (e : expr) : tactic (expr × list expr × expr) :=
do tp ← infer_type e, match tp with
| `(%%lhs ≤ %%rhs) := prove_inequality lhs rhs e gen_comp.le
| `(%%lhs < %%rhs) := prove_inequality lhs rhs e gen_comp.lt
| `(%%lhs ≥ %%rhs) := prove_inequality lhs rhs e gen_comp.ge
| `(%%lhs > %%rhs) := prove_inequality lhs rhs e gen_comp.gt
| `(%%lhs = %%rhs) := prove_inequality lhs rhs e gen_comp.eq
| `(%%lhs ≠ %%rhs) := prove_inequality lhs rhs e gen_comp.ne
| _ := do s ← to_string <$> pp e, fail $ "didn't recognize " ++ s
end

section aux

meta def mk_neg : expr → expr
| `((-%%lhs) * %%rhs) := `(%%lhs * %%rhs : α)
| `(%%lhs * %%rhs) := `((-%%lhs) * %%rhs : α)
| a := `((-1 : α) * %%a)

meta def get_sum_components : expr → list expr
| `(%%lhs + %%rhs) := rhs::(get_sum_components lhs)
| `(%%lhs - %%rhs) := mk_neg rhs::(get_sum_components lhs)
| a := [a]

meta def get_prod_components : expr → list expr
| `(%%lhs * %%rhs) := rhs::(get_prod_components lhs)
| a := [a]

meta def is_sum (e : expr) : bool :=
e.is_app_of ``has_add.add || e.is_app_of ``has_sub.sub

meta def is_prod (e : expr) : bool :=
e.is_app_of ``has_mul.mul || e.is_app_of ``rat.pow

open tactic
meta def get_comps_of_mul (e : expr) : tactic (expr × α) := match e with
| `(%%lhs * %%rhs) := (do c ← eval_expr α lhs, return (rhs, c)) <|> return (e, 1)
| `(%%num / %%denom) := (do c ← eval_expr α denom, return (num, 1/c)) <|> return (e, 1)
| f := return (f, 1)
end

meta def get_comps_of_exp (e : expr) : tactic (expr × ℤ) := match e with
| `(rat.pow %%base %%exp) := (do z ← eval_expr ℤ exp, return (base, z)) <|> return (e, 1)
| f := return (f, 1)
end

end aux

end polya