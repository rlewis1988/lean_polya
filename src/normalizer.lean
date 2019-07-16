import datatypes -- blackboard

namespace field
variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

namespace nterm

def mk_unit : nterm γ → nterm γ × γ
| (nterm.const c) := (1, c)
| (nterm.mul t (nterm.const c)) := (t, c)
| t := (t, 1)

theorem eval_mk_unit {t nt : nterm γ} {c : γ} :
  mk_unit t = (nt, c) → nterm.eval ρ t = nterm.eval ρ nt * c :=
begin
  intro h,
  cases t,
  case mul : x y {
    cases y,
    case const : c {
      unfold mk_unit at h, rw [prod.mk.inj_iff] at h,
      cases h with h1 h2, subst h1, subst h2,
      simp [eval] },
    repeat {
      unfold mk_unit at h, rw [prod.mk.inj_iff] at h,
      cases h with h1 h2, subst h1, subst h2,
      simp [eval] }},
  repeat {
    unfold mk_unit at h, rw [prod.mk.inj_iff] at h,
    cases h with h1 h2, subst h1, subst h2,
    simp [eval] }
end

def scale (t : nterm γ) (a : γ) : nterm γ :=
if a = 0 then
  0
else if a = 1 then
  t
else match t with
| (nterm.const b) := (b * a : γ)
| (nterm.mul t (nterm.const b)) :=
  if b * a = 1 then t else t * ↑(b * a : γ)
| t := t * a
end

theorem eval_scale {t : nterm γ} {a : γ} :
  nterm.eval ρ (scale t a) = nterm.eval ρ t * a :=
begin
  by_cases h1 : a = 0,
  { simp [scale, h1] },
  by_cases h2 : a = 1,
  { simp [scale, h1, h2] },
  cases t, case mul : x y
  { cases y, case const : b
    { by_cases h3 : b * a = 1,
      { unfold scale,
        rw [if_neg h1, if_neg h2, if_pos h3],
        unfold eval, --todo: fix norm_cast
        rw [mul_assoc, ← morph.morph_mul],
        rw [h3, morph.morph1, mul_one] },
      { unfold scale,
        rw [if_neg h1, if_neg h2, if_neg h3],
        unfold eval,
        rw [mul_assoc, ← morph.morph_mul],
        rw [nterm.eval_mul, nterm.eval_const],
        refl }},
    repeat { simp [scale, h1, h2, eval] }},
  repeat { simp [scale, h1, h2, eval] }
end

def scale2 (t1 t2 : nterm γ) : nterm γ × nterm γ × γ :=
if t1.mk_unit.snd = 0 then
  (0, t2, 1)
else
  (t1.mk_unit.fst, t2.scale (t1.mk_unit.snd⁻¹), t1.mk_unit.snd)

def scale2_eval {t1 t2 nt1 nt2 : nterm γ} {c : γ} :
  scale2 t1 t2 = (nt1, nt2, c) → nterm.eval ρ ( t1 - t2 ) = nterm.eval ρ ( (nt1 - nt2) * c ) :=
begin
  intro h, unfold scale2 at h,
  by_cases h0 : t1.mk_unit.snd = 0,
  { rw [if_pos h0, prod.mk.inj_iff, prod.mk.inj_iff] at h,
    cases h with h1 h, cases h with h2 h3,
    subst h1, subst h2, subst h3,
    have h4 : nterm.eval ρ t1 = 0, by {
      rw eval_mk_unit,
      { rw [morph.morph0, mul_zero] },
      { rw [← h0, prod.mk.eta] }},
    simp [h4] },
  rw [if_neg h0, prod.mk.inj_iff, prod.mk.inj_iff] at h,
  cases h with h1 h, cases h with h2 h3,
  rw [h3] at h0 h2,
  have : (c : α) ≠ 0, by {
    intro h, apply h0, --todo: norm_cast should work after the update
    apply morph.morph_inj c h },
  have hl : nterm.eval ρ nt1 = nterm.eval ρ t1 / c,
  by {
    apply eq.symm, apply (div_eq_iff_mul_eq this).mpr,
    apply eq.symm, apply eval_mk_unit,
    rw [← h1, ← h3, prod.mk.eta] },
  have hr : nterm.eval ρ nt2 = nterm.eval ρ t2 / c,
  by {
    rw [← h2, eval_scale, division_def],
    { norm_cast }},
  rw [nterm.eval_mul, nterm.eval_const, nterm.eval_sub, nterm.eval_sub],
  rw [sub_mul, hl, hr],
  rw [div_mul_eq_mul_div_comm _ _ this, div_mul_eq_mul_div_comm _ _ this],
  rw [div_self this, mul_one, mul_one],
end

end nterm

open nterm

def mk_unit2 (t1 t2 : nterm γ) : nterm γ × nterm γ × γ :=
match t1.mk_unit, t2.mk_unit with
| (t1', c1), (t2', c2) :=
  if c1 = 0 then
    (t2', 0, -c2)
  else if c2 = 0 then
    (t1', 0, c1)
  else if t1' ≤ t2' then
    (t1', scale t2' (c2 / c1), c1)
  else
    (t2', scale t1' (c1 / c2), -c2)
end

private lemma mk_unit2_def_1 {t1 t2 : nterm γ} :
  t1.mk_unit.snd = 0 →
  mk_unit2 t1 t2 = (t2.mk_unit.fst, 0, -t2.mk_unit.snd) :=
begin
  intro h1,
  unfold mk_unit2,
  cases t1.mk_unit with t1 c1,
  cases t2.mk_unit with t2 c2,
  unfold mk_unit2._match_1, --??
  rw [if_pos h1]
end

private lemma mk_unit2_def_2 {t1 t2 : nterm γ} :
  t1.mk_unit.snd ≠ 0 →
  t2.mk_unit.snd = 0 →
  mk_unit2 t1 t2 = (t1.mk_unit.fst, 0, t1.mk_unit.snd) :=
begin
  intros h1 h2,
  unfold mk_unit2,
  cases t1.mk_unit with t1 c1,
  cases t2.mk_unit with t2 c2,
  unfold mk_unit2._match_1, --??
  rw [if_neg h1, if_pos h2]
end

private lemma mk_unit2_def_3 {t1 t2 : nterm γ} :
  t1.mk_unit.snd ≠ 0 →
  t2.mk_unit.snd ≠ 0 →
  t1.mk_unit.fst ≤ t2.mk_unit.fst →
  mk_unit2 t1 t2 =
  ( t1.mk_unit.fst,
    t2.mk_unit.fst.scale (t2.mk_unit.snd / t1.mk_unit.snd),
    t1.mk_unit.snd ) :=
begin
  intros h1 h2 h3,
  unfold mk_unit2,
  cases t1.mk_unit with t1 c1,
  cases t2.mk_unit with t2 c2,
  unfold mk_unit2._match_1, --??
  rw [if_neg h1, if_neg h2, if_pos h3]
end

private lemma mk_unit2_def_4 {t1 t2 : nterm γ} :
  t1.mk_unit.snd ≠ 0 →
  t2.mk_unit.snd ≠ 0 →
  ¬ t1.mk_unit.fst ≤ t2.mk_unit.fst →
  mk_unit2 t1 t2 =
  ( t2.mk_unit.fst,
    t1.mk_unit.fst.scale (t1.mk_unit.snd / t2.mk_unit.snd),
    -t2.mk_unit.snd ) :=
begin
  intros h1 h2 h3,
  unfold mk_unit2,
  cases t1.mk_unit with t1 c1,
  cases t2.mk_unit with t2 c2,
  unfold mk_unit2._match_1, --??
  rw [if_neg h1, if_neg h2, if_neg h3]
end

theorem eval_mk_unit2 {t1 t2 t3 t4 : nterm γ} {c : γ} :
  (t3, t4, c) = mk_unit2 t1 t2 →
  nterm.eval ρ t1 - nterm.eval ρ t2 =
    (nterm.eval ρ t3 - nterm.eval ρ t4) * c :=
begin
  intro h0,
  by_cases h1 : t1.mk_unit.snd = 0,
  { rw mk_unit2_def_1 h1 at h0,
    simp only [prod.mk.inj_iff] at h0,
    cases h0 with h4 h5, cases h5 with h5 h6,
    subst h4, subst h5, subst h6,
    rw [eval_mk_unit (eq.symm prod.mk.eta), h1, morph.morph0, mul_zero, zero_sub],
    rw [morph.morph_neg, mul_neg_eq_neg_mul_symm, nterm.eval_zero, sub_zero, ← eval_mk_unit],
    apply (eq.symm prod.mk.eta) },
  by_cases h2 : t2.mk_unit.snd = 0,
  { rw mk_unit2_def_2 h1 h2 at h0,
    simp only [prod.mk.inj_iff] at h0,
    cases h0 with h4 h5, cases h5 with h5 h6,
    subst h4, subst h5, subst h6,
    rw [eval_mk_unit (eq.symm (@prod.mk.eta _ _ (mk_unit t2))), h2, morph.morph0, mul_zero, sub_zero],
    rw [nterm.eval_zero, sub_zero, eval_mk_unit],
    apply (eq.symm prod.mk.eta) },
  by_cases h3 : t1.mk_unit.fst ≤ t2.mk_unit.fst,
  { rw mk_unit2_def_3 h1 h2 h3 at h0,
    simp only [prod.mk.inj_iff] at h0,
    cases h0 with h4 h5, cases h5 with h5 h6,
    subst h4, subst h5, subst h6,
    rw [sub_mul, ← eval_mk_unit (eq.symm prod.mk.eta)],
    rw [eval_scale, morph.morph_div, ← mul_div_assoc, div_mul_cancel],
    { rw ← eval_mk_unit, apply (eq.symm prod.mk.eta) },
    { intro contrad, rw [← morph.morph0 γ, morph.morph_inj'] at contrad,
      apply h1 contrad }}, --todo: norm_cast
  { rw mk_unit2_def_4 h1 h2 h3 at h0,
    simp only [prod.mk.inj_iff] at h0,
    cases h0 with h4 h5, cases h5 with h5 h6,
    subst h4, subst h5, subst h6,
    rw [morph.morph_neg, mul_neg_eq_neg_mul_symm, ← neg_mul_eq_neg_mul_symm, neg_sub],
    rw [sub_mul, ← eval_mk_unit (eq.symm prod.mk.eta)],
    rw [eval_scale, morph.morph_div, ← mul_div_assoc, div_mul_cancel],
    { rw ← eval_mk_unit, apply (eq.symm prod.mk.eta) },
    { intro contrad, rw [← morph.morph0 γ, morph.morph_inj'] at contrad,
      apply h2 contrad }}, --todo: norm_cast
end

def norm2 (t1 t2 : eterm γ) : nterm γ × nterm γ × γ :=
  mk_unit2 (norm t1) (norm t2)

theorem eval_norm2 {t1 t2 : eterm γ} {nt1 nt2 : nterm γ} {c : γ} :
  nonzero ρ t1.to_nterm.norm_hyps →
  nonzero ρ t2.to_nterm.norm_hyps →
  (nt1, nt2, c) = norm2 t1 t2 →
  eterm.eval ρ t1 - eterm.eval ρ t2 =
    (nterm.eval ρ nt1 - nterm.eval ρ nt2) * c :=
begin
  intros nz1 nz2 h0,
  cases (norm t1).mk_unit with nt1 c1,
  cases (norm t2).mk_unit with nt2 c2,
  unfold norm2 at h0,
  apply eq.trans,
  { show _ = nterm.eval ρ (norm t1) - nterm.eval ρ (norm t2),
    rw [correctness nz1, correctness nz2] },
  { apply eval_mk_unit2 h0 }
end

end field

@[reducible] def α := ℚ

namespace polya

namespace gen_comp

--def to_rel : gen_comp → ℝ → ℝ → Prop
--| le := (≤)
--| lt := (<)
--| ge := (≥)
--| gt := (>)
--| eq := (=)
--| ne := (≠)

section
variables {u v x y a : α} --TODO: more general hypothesis?

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
  e ← to_expr ``(%%foo %%pr1 %%pr3 %%pr2),
  --e ← mk_app decl [pr1, pr3, pr2],
  return e

end gen_comp

open tactic field tactic.field

meta def prove_inequality (lhs rhs pf : expr) (op : gen_comp) :
  tactic (expr × list expr × expr) :=
do
  (t1, s) ← (eterm_of_expr lhs).run ∅,
  (t2, s) ← (eterm_of_expr rhs).run s,
  ρ ← s.dict_expr,

  (mvars1, h_aux_1) ← prove_norm_hyps t1 s,
  (mvars2, h_aux_2) ← prove_norm_hyps t2 s,

  let (t1', t2', c) := norm2 t1 t2,
  lhs' ← nterm_to_expr `(α) s t1',
  rhs' ← nterm_to_expr `(α) s t2',
  let c_expr : expr := reflect c,
  let op' := if c > 0 then op else op.reverse,

  h_aux_3 ← to_expr ``((%%(reflect t1'), %%(reflect t2'), %%(c_expr)) = norm2 %%(reflect t1) %%(reflect t2))
    >>= mk_meta_var,
  
  e1 ← to_expr ``(%%lhs - %%rhs),
  e2 ← to_expr ``(eterm.eval %%ρ %%(reflect t1) - eterm.eval %%ρ %%(reflect t2)),
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
| `((-%%lhs) * %%rhs) := `(%%lhs * %%rhs : ℚ)
| `(%%lhs * %%rhs) := `((-%%lhs) * %%rhs : ℚ)
| a := `((-1 : ℚ)*%%a)

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
meta def get_comps_of_mul (e : expr) : tactic (expr × ℚ) := match e with
| `(%%lhs * %%rhs) := (do c ← eval_expr ℚ lhs, return (rhs, c)) <|> return (e, 1)
| `(%%num / %%denom) := (do c ← eval_expr ℚ denom, return (num, 1/c)) <|> return (e, 1)
| f := return (f, 1)
end

meta def get_comps_of_exp (e : expr) : tactic (expr × ℤ) := match e with
| `(rat.pow %%base %%exp) := (do z ← eval_expr ℤ exp, return (base, z)) <|> return (e, 1)
| f := return (f, 1)
end

end aux

end polya
