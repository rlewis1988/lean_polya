import .nterm

namespace polya

open nterm

variables {α : Type} [discrete_field α]
variables {γ : Type} [coeff γ]
variables [morph γ α] {ρ : dict α}

structure cterm : Type :=
(term : @nterm γ _)
(coeff : γ)

namespace cterm

def le (x y : @cterm γ _) : Prop := x.term ≤ y.term

instance : has_le (@cterm γ _) := ⟨le⟩
instance : decidable_rel (@cterm.le γ _) := by delta cterm.le; apply_instance

def mul (x : @cterm γ _) (a : γ) : @cterm γ _ :=
⟨x.term, x.coeff * a⟩

def of_nterm (x : @nterm γ _) : @cterm γ _ :=
⟨x, 1⟩

def to_nterm (x : @cterm γ _) : @nterm γ _ :=
if x.coeff = 0 then 0
else if x.coeff = 1 then x.term
else x.term * x.coeff

def eval (ρ : dict α) (x : @cterm γ _) : α :=
x.term.eval ρ * morph.f _ x.coeff

theorem eval_def {x : @nterm γ _} {a : γ} :
  eval ρ ⟨x, a⟩ = x.eval ρ * morph.f _ a :=
rfl

theorem eval_to_nterm (x : @cterm γ _) :
  x.to_nterm.eval ρ = x.eval ρ :=
begin
  unfold to_nterm, unfold eval,
  by_cases h1 : x.coeff = 0,
  { simp [h1] },
  { by_cases h2 : x.coeff = 1,
    { simp [h2] },
    { simp [h1, h2] }}
end

theorem eval_to_nterm' :
  @nterm.eval _ _ γ _ _ ρ ∘ cterm.to_nterm = cterm.eval ρ :=
begin
  unfold function.comp,
  simp [eval_to_nterm]
end

theorem eval_mul (x : @cterm γ _) (a : γ) :
  (x.mul a).eval ρ = x.eval ρ * (morph.f _ a) :=
begin
  simp [mul, eval], 
  rw mul_assoc
end

end cterm

structure sterm : Type :=
(terms : list (@cterm γ _))

namespace sterm

def append (S1 S2 : @sterm γ _) : @sterm γ _ :=
⟨S1.terms ++ S2.terms⟩

instance : has_append (@sterm γ _) := ⟨append⟩

theorem append_terms (S1 S2 : @sterm γ _) :
  (S1 ++ S2).terms = S1.terms ++ S2.terms := rfl

def mul (S : @sterm γ _) (a : γ) : @sterm γ _ :=
if a = 0 then ⟨[]⟩
else if a = 1 then S
else ⟨S.terms.map (λ x, x.mul a)⟩

def eval (ρ : dict α) (S : @sterm γ _) : α :=
list.sum (S.terms.map (cterm.eval ρ))

theorem eval_mul (S : @sterm γ _) (a : γ) :
(S.mul a).eval ρ = S.eval ρ * morph.f _ a :=
begin
  by_cases h : a = 0 ∨ a = 1,
  { cases h with h h,
    { simp [h, mul, eval] },
    { simp [h, mul, eval] }},
  { have h0 : ¬ a = 0, by { intro h0, apply h, left, exact h0 },
    have h1 : ¬ a = 1, by { intro h1, apply h, right, exact h1 },
    cases S with terms,
    simp [h0, h1, mul, eval], 
    induction terms with x xs ih,
    { simp },
    { simp [ih, add_mul, cterm.eval_mul] }
  }
end

theorem eval_add (S1 S2 : @sterm γ _) :
  (S1 ++ S2).eval ρ = S1.eval ρ + S2.eval ρ :=
begin
  unfold eval,
  simp only [append_terms],
  rw [list.map_append],
  apply list.sum_append 
end

def to_nterm (S : @sterm γ _) : @nterm γ _ :=
sum (S.terms.map (cterm.to_nterm))

theorem eval_to_nterm {S : @sterm γ _} :
  S.eval ρ = S.to_nterm.eval ρ :=
begin
  cases S with terms,
  unfold to_nterm, unfold eval,
  rw [eval_sum, list.map_map],
  rw cterm.eval_to_nterm'
end

def reduce_aux : @cterm γ _ → list (@cterm γ _) → list (@cterm γ _)
| x []      := [x] --TODO
| x (y::ys) :=
  if x.term = y.term then
    reduce_aux ⟨x.term, x.coeff + y.coeff⟩ ys
  else if x.coeff = 0 then
    reduce_aux y ys
  else
    x::(reduce_aux y ys)
  
theorem eval_reduce_aux (x : @cterm γ _) (xs : list (@cterm γ _)) :
  sterm.eval ρ ⟨reduce_aux x xs⟩ = sterm.eval ρ ⟨x::xs⟩ :=
begin
  revert x,
  induction xs with y ys ih,
  { simp [eval, reduce_aux] },
  { intro x,
    unfold eval,
    rw [list.map_cons, list.sum_cons],
    unfold eval at ih,
    by_cases h1 : x.term = y.term,
    { rw [list.map_cons, list.sum_cons],
      rw [← add_assoc],
      unfold cterm.eval,
      rw [h1, ← mul_add, ← morph.morph_add],
      rw [← cterm.eval_def, ← list.sum_cons, ← list.map_cons],
      rw [← ih],
      simp [reduce_aux, h1] },
    by_cases h2 : x.coeff = 0,
    { rw [list.map_cons, list.sum_cons],
      unfold cterm.eval,
      rw [h2, morph.morph0, mul_zero, zero_add],
      rw [← cterm.eval_def, ← list.sum_cons, ← list.map_cons],
      simp [reduce_aux, h1, h2, ih], refl
    },
    conv {
      to_lhs,
      simp [reduce_aux, h1, h2]
    },
    simp [ih]
  }
end

def reduce (S : @sterm γ _) : @sterm γ _ :=
match S.terms with
| []      := ⟨[]⟩
| (x::xs) := ⟨reduce_aux x xs⟩
end
 
theorem eval_reduce {S : @sterm γ _} :
  S.eval ρ = S.reduce.eval ρ :=
begin
  cases S with terms,
  cases terms with x xs,
  { simp [reduce] },
  { simp [reduce, eval_reduce_aux] }
end

def sort (S : @sterm γ _) : @sterm γ _ :=
⟨S.terms.merge_sort (≤)⟩

theorem eval_sort {S : @sterm γ _} :
  S.eval ρ = S.sort.eval ρ :=
begin
  unfold eval, unfold sort,
  apply list.sum_eq_of_perm,
  apply list.perm_map,
  apply list.perm.symm,
  apply list.perm_merge_sort
end

end sterm

namespace nterm

def to_sterm : @nterm γ _ → @sterm γ _
| (add x y) := x.to_sterm ++ y.to_sterm
| (mul x y) :=
  match x with
  | (const a) := y.to_sterm.mul a
  | _         :=
    match y with
    | (const b) := x.to_sterm.mul b
    | _         := ⟨[⟨mul x y, 1⟩]⟩
    end
  end
| x := ⟨[⟨x, 1⟩]⟩

theorem eval_to_sterm {x : @nterm γ _} :
  nterm.eval ρ x = sterm.eval ρ x.to_sterm :=
begin
  induction x with i c x y ihx ihy x y ihx ihy x n ihx,
  { simp [to_sterm, nterm.eval, sterm.eval, cterm.eval] },
  { simp [to_sterm, nterm.eval, sterm.eval, cterm.eval] },
  { unfold to_sterm, unfold eval,
    rw [sterm.eval_add, ihx, ihy] },
  { cases x,
    case const : a {
      simp only [to_sterm, sterm.eval_mul, eval, ihy],
      exact mul_comm (morph.f α a) _
    },
    repeat {
      cases y,
      case const : b {
        simp only [to_sterm, sterm.eval_mul, eval, ihx]
      },
      repeat { simp [to_sterm, nterm.eval, sterm.eval, cterm.eval] },
    }
  },
  { simp [to_sterm, nterm.eval, sterm.eval, cterm.eval] }

end

def norm (x : @nterm γ _) : @nterm γ _ :=
x.to_sterm.sort.reduce.to_nterm

theorem correctness {x : @nterm γ _} :
  x.eval ρ = x.norm.eval ρ :=
calc
  x.eval ρ = sterm.eval ρ x.to_sterm             : eval_to_sterm
       ... = sterm.eval ρ x.to_sterm.sort        : sterm.eval_sort
       ... = sterm.eval ρ x.to_sterm.sort.reduce : sterm.eval_reduce
       ... = nterm.eval ρ x.norm                 : sterm.eval_to_nterm

end nterm

end polya
