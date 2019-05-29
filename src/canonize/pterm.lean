import .nterm

namespace list

theorem filter_perm {α} {p : α → Prop} [decidable_pred p] {l : list α} :
  l ~ l.filter p ++ l.filter (not ∘ p) :=
begin
  induction l with x xs ih,
  { simp },
  { by_cases hx : p x,
    { simp [filter, hx, perm.skip, ih] },
    { calc
      x::xs ~ x::(filter p xs ++ filter (not ∘ p) xs) : perm.skip _ ih
      ... ~ filter p xs ++ x::filter (not ∘ p) xs : perm.symm perm_middle
      ... ~ filter p (x::xs) ++ filter (not ∘ p) (x::xs) : by simp [hx] }}
end

theorem prod_ones {α} [monoid α] {l : list α} :
  (∀ x : α, x ∈ l → x = 1) → l.prod = 1 :=
begin
  intro h,
  induction l with x xs ih,
  { refl },
  { have h1 : x = 1, by { apply h, simp },
    have h2 : prod xs = 1, by { apply ih, intros _ hx, apply h, simp [hx] },
    simp [h1, h2] }
end

end list

namespace polya

open nterm

variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

--@[derive decidable_eq]
structure xterm : Type :=
(term : @nterm γ _)
(exp : znum)

namespace xterm

def le (x y : @xterm γ _) : Prop := x.term ≤ y.term

instance : has_le (@xterm γ _) := ⟨le⟩
instance : decidable_rel (@xterm.le γ _) := by delta xterm.le; apply_instance

def to_nterm (x : @xterm γ _) : @nterm γ _ :=
if x.exp = 0 then x.term / x.term
else if x.exp = 1 then x.term
else x.term ^ x.exp

def eval (ρ : dict α) (x : @xterm γ _) : α :=
let a := nterm.eval ρ x.term in
if a = 0 then 0 else a ^ (x.exp : ℤ)

def eval_to_nterm {x : @xterm γ _} :
 nterm.eval ρ x.to_nterm = xterm.eval ρ x :=
begin
  by_cases hx : nterm.eval ρ x.term = 0;
  { by_cases h1 : x.exp = 0,
    { simp [hx, h1, nterm.eval, xterm.eval, to_nterm] },
    { have : (x.exp : ℤ) ≠ 0, by {rw ← znum.cast_zero, exact_mod_cast h1 },
      by_cases h2 : x.exp = 1;
      simp [hx, h1, h2, nterm.eval, xterm.eval, to_nterm, zero_fpow, this] }}
end

theorem eval_to_nterm' :
  @nterm.eval _ _ γ _ _ ρ ∘ xterm.to_nterm = xterm.eval ρ :=
begin
  unfold function.comp,
  simp [eval_to_nterm]
end

theorem eval_def {x : @nterm γ _} {n : znum} :
  xterm.eval ρ ⟨x, n⟩ =
    if nterm.eval ρ x = 0 then 0
    else nterm.eval ρ x ^ (n : ℤ) :=
rfl

theorem eval_add {x : @nterm γ _} {n m : znum} :
  xterm.eval ρ ⟨x, n + m⟩ = xterm.eval ρ ⟨x, n⟩ * xterm.eval ρ ⟨x, m⟩ :=
begin
  by_cases hx : nterm.eval ρ x = 0;
  simp [xterm.eval, fpow_add, hx]
end

end xterm

structure pterm : Type :=
(terms : list (@xterm γ _))
(coeff : γ)

namespace pterm

instance : has_zero (@pterm γ _) :=
⟨{ terms := [],
   coeff := 0,
}⟩

instance : has_one (@pterm γ _) :=
⟨{ terms := [],
   coeff := 1,
}⟩

def eval (ρ : dict α) (P : @pterm γ _) : α :=
list.prod (P.terms.map (xterm.eval ρ)) * morph.f _ P.coeff

def mul (P1 P2 : @pterm γ _) : @pterm γ _ :=
if P1.coeff = 0 ∨ P2.coeff = 0 then
  { terms := [],
    coeff := 0,
  }
else
  { terms := P1.terms ++ P2.terms,
    coeff := P1.coeff * P2.coeff,
  }

def pow (P : @pterm γ _) (m : znum) : @pterm γ _ :=
if m = 0 then 1
else
  { terms := P.terms.map (λ ⟨x, n⟩, ⟨x, n + m⟩),
    coeff := P.coeff ^ (m : ℤ),
  }

instance : has_mul (@pterm γ _) := ⟨mul⟩
instance : has_pow (@pterm γ _) znum := ⟨pow⟩

theorem mul_terms {P Q : @pterm γ _} :
  P.coeff ≠ 0 ∧ Q.coeff ≠ 0 →
  (P * Q).terms = P.terms ++ Q.terms :=
begin
  intro h,
  simp [has_mul.mul, mul, h] 
end

theorem mul_terms' {P Q : @pterm γ _} :
  P.coeff = 0 ∨ Q.coeff = 0 →
  (P * Q).terms = [] :=
begin
  intro h,
  simp [has_mul.mul, mul, h]
end

theorem mul_coeff {P Q : @pterm γ _} :
  (P * Q).coeff = P.coeff * Q.coeff :=
begin
  by_cases h : P.coeff = 0 ∨ Q.coeff = 0,
  { apply eq.trans,
    { show (P * Q).coeff = 0, simp [has_mul.mul, mul, h] },
    { simp [h] }},
  { simp [has_mul.mul, mul, h] }
end

theorem eval_mul {P Q : @pterm γ _} :
  pterm.eval ρ (P * Q) = pterm.eval ρ P * pterm.eval ρ Q :=
begin
  unfold pterm.eval, rw mul_coeff,
  by_cases h0 : P.coeff = 0 ∨ Q.coeff = 0,
  { cases h0; simp [h0, morph.morph0] },
  { have : P.coeff ≠ 0 ∧ Q.coeff ≠ 0,
    from (decidable.not_or_iff_and_not _ _).mp h0,
    rw [mul_terms this, list.map_append, list.prod_append, morph.morph_mul],
    ring }
end

def to_nterm (P : @pterm γ _) : @nterm γ _ :=
prod (P.terms.map (xterm.to_nterm)) * P.coeff

theorem eval_to_nterm {P : @pterm γ _} :
  pterm.eval ρ P = nterm.eval ρ P.to_nterm :=
begin
  cases P with terms coeff ts,
  suffices : list.prod (list.map (xterm.eval ρ) terms) * morph.f α coeff =
    nterm.eval ρ (prod (list.map xterm.to_nterm terms)) * morph.f α coeff,
  by simp [to_nterm, pterm.eval, this],
  rw [eval_prod, list.map_map],
  rw xterm.eval_to_nterm'
end

def filter (P : @pterm γ _) : @pterm γ _ :=
{ terms := P.terms.filter (λ x, x.exp ≠ 0),
  coeff := P.coeff
}

def filter_hyps (P : @pterm γ _) : list (@nterm γ _) :=
list.map xterm.term (P.terms.filter (λ x, x.exp = 0))

private lemma lemma_eval_filter {x : @xterm γ _} :
  x.exp = 0 ∧ nterm.eval ρ x.term ≠ 0 →
  xterm.eval ρ x = 1 :=
begin
  cases x with x n,
  simp only [],
  intro h, cases h with hn hx,
  simp [xterm.eval, hn, hx]
end

theorem eval_filter {P : @pterm γ _} :
  (0 : α) ∉ P.filter_hyps.map (nterm.eval ρ) →
  pterm.eval ρ P = pterm.eval ρ P.filter :=
begin
  intro H,
  have H1 : ∀ x : xterm, x ∈ P.terms → x.exp = 0 → nterm.eval ρ (x.term) ≠ 0,
  by simpa [filter_hyps] using H,
  have H2 : ∀ x : xterm, x ∈ P.terms.filter (λ x, x.exp = 0) → nterm.eval ρ (x.term) ≠ 0,
  by { intros x hx, have : x ∈ P.terms ∧ x.exp = 0, from list.mem_filter.mp hx,
       cases this, apply H1; assumption },

  have : P.terms ~ P.terms.filter (λ x, x.exp = 0) ++ P.terms.filter (λ x, x.exp ≠ 0),
  from list.filter_perm,

  unfold pterm.eval,
  rw list.prod_eq_of_perm (list.perm_map _ this),
  rw [list.map_append, list.prod_append],

  have : ∀ x ∈ P.terms.filter (λ x, x.exp = 0), xterm.eval ρ x = 1,
  by {
    intros x hx,
    apply lemma_eval_filter,
    split,
    { exact (list.mem_filter.mp hx).right },
    { apply H2, exact hx }},

  have : ∀ a ∈ (list.map (xterm.eval ρ) (P.terms.filter (λ x, x.exp = 0))), a = 1,
  by { intros a ha, rw list.mem_map at ha,
    cases ha with x hx,
    cases hx with hx ha,
    rw ← ha, apply this,
    assumption },

  simp [filter, list.prod_ones this]
end

end pterm

end polya
