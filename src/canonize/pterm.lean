import .nterm

namespace polya

open nterm

variables {α : Type} [discrete_field α]
variables {γ : Type} [coeff γ]
variables [morph γ α] {ρ : dict α}

structure xterm : Type :=
(term : @nterm γ _)
(exp : znum)

namespace xterm

def le (x y : @xterm γ _) : Prop := x.term ≤ y.term

instance : has_le (@xterm γ _) := ⟨le⟩
instance : decidable_rel (@xterm.le γ _) := by delta xterm.le; apply_instance

def pow (x : @xterm γ _) (n : znum) : @xterm γ _ :=
⟨x.term, x.exp * n⟩

def of_nterm (x : @nterm γ _) : @xterm γ _ :=
⟨x, 1⟩

def to_nterm (x : @xterm γ _) : @nterm γ _ :=
if x.exp = 0 then 1
else if x.exp = 1 then x.term
else x.term ^ x.exp

def eval (ρ : dict α) (x : @xterm γ _) : α :=
x.term.eval ρ ^ (x.exp : ℤ)

theorem eval_def {x : @nterm γ _} {n : znum} :
  eval ρ ⟨x, n⟩ = x.eval ρ ^ (n : ℤ) :=
rfl

theorem eval_to_nterm (x : @xterm γ _) :
  x.to_nterm.eval ρ = x.eval ρ :=
begin
  unfold to_nterm, unfold eval,
  by_cases h1 : x.exp = 0,
  { simp [h1] },
  { by_cases h2 : x.exp = 1,
    { simp [h2] },
    { simp [h1, h2] }}
end

theorem eval_to_nterm' :
  @nterm.eval _ _ γ _ _ ρ ∘ xterm.to_nterm = xterm.eval ρ :=
begin
  unfold function.comp,
  simp [eval_to_nterm]
end

theorem eval_pow {x : @xterm γ _} {n : znum} :
  (x.pow n).eval ρ = x.eval ρ ^ (n : ℤ) :=
by simp [pow, eval, fpow_mul] 

end xterm

structure pterm : Type :=
(terms : list (@xterm γ _))

namespace pterm

def append (S1 S2 : @pterm γ _) : @pterm γ _ :=
⟨S1.terms ++ S2.terms⟩

instance : has_append (@pterm γ _) := ⟨append⟩

theorem append_terms (S1 S2 : @pterm γ _) :
  (S1 ++ S2).terms = S1.terms ++ S2.terms := rfl

def pow (S : @pterm γ _) (n : znum) : @pterm γ _ :=
if n = 0 then ⟨[]⟩
else if n = 1 then S
else ⟨S.terms.map (λ x, x.pow n)⟩

def eval (ρ : dict α) (S : @pterm γ _) : α :=
list.prod (S.terms.map (xterm.eval ρ))

theorem eval_pow (S : @pterm γ _) (n : znum) :
(S.pow n).eval ρ = S.eval ρ ^ (n : ℤ) :=
begin
  by_cases h : n = 0 ∨ n = 1,
  { cases h with h h,
    { simp [h, pow, eval] },
    { simp [h, pow, eval] }},
  { have h0 : ¬ n = 0, by { intro h0, apply h, left, exact h0 },
    have h1 : ¬ n = 1, by { intro h1, apply h, right, exact h1 },
    cases S with terms,
    simp [h0, h1, pow, eval], 
    induction terms with x xs ih,
    { simp },
    { simp [ih, mul_fpow, xterm.eval_pow] }
  }
end

theorem eval_mul (S1 S2 : @pterm γ _) :
  (S1 ++ S2).eval ρ = S1.eval ρ * S2.eval ρ :=
begin
  unfold eval,
  simp only [append_terms],
  rw [list.map_append],
  apply list.prod_append 
end

def to_nterm (S : @pterm γ _) : @nterm γ _ :=
prod (S.terms.map (xterm.to_nterm))

theorem eval_to_nterm {S : @pterm γ _} :
  S.eval ρ = S.to_nterm.eval ρ :=
begin
  cases S with terms,
  unfold to_nterm, unfold eval,
  rw [eval_prod, list.map_map],
  rw xterm.eval_to_nterm'
end

def reduce_aux : @xterm γ _ → list (@xterm γ _) → list (@xterm γ _)
| x []      := [x] --TODO
| x (y::ys) :=
  if x.term = y.term then
    reduce_aux ⟨x.term, x.exp + y.exp⟩ ys
  else if x.exp = 0 then
    reduce_aux y ys
  else
    x::(reduce_aux y ys)
  
theorem eval_reduce_aux (x : @xterm γ _) (xs : list (@xterm γ _)) :
  pterm.eval ρ ⟨reduce_aux x xs⟩ = pterm.eval ρ ⟨x::xs⟩ :=
begin
  revert x,
  induction xs with y ys ih,
  { simp [eval, reduce_aux] },
  { intro x,
    unfold eval,
    rw [list.map_cons, list.prod_cons],
    unfold eval at ih,
    by_cases h1 : x.term = y.term,
    { rw [list.map_cons, list.prod_cons],
      rw [← mul_assoc],
      unfold xterm.eval,
      rw [h1, ← fpow_add],
      { norm_cast,
        rw [← xterm.eval_def, ← list.prod_cons, ← list.map_cons],
        rw [← ih],
        simp [reduce_aux, h1] },
      { sorry }}, -- TODO: introduce hypothesis
    by_cases h2 : x.exp = 0,
    { rw [list.map_cons, list.prod_cons],
      unfold xterm.eval,
      rw_mod_cast [h2, fpow_zero],
      rw [← xterm.eval_def, ← list.prod_cons, ← list.map_cons],
      simp [reduce_aux, h1, h2, ih], refl
    },
    conv {
      to_lhs,
      simp [reduce_aux, h1, h2]
    },
    simp [ih]
  }
end

def reduce (S : @pterm γ _) : @pterm γ _ :=
match S.terms with
| []      := ⟨[]⟩
| (x::xs) := ⟨reduce_aux x xs⟩
end
 
theorem eval_reduce {S : @pterm γ _} :
  S.eval ρ = S.reduce.eval ρ :=
begin
  cases S with terms,
  cases terms with x xs,
  { simp [reduce] },
  { simp [reduce, eval_reduce_aux] }
end

def sort (S : @pterm γ _) : @pterm γ _ :=
⟨S.terms.merge_sort (≤)⟩

theorem eval_sort {S : @pterm γ _} :
  S.eval ρ = S.sort.eval ρ :=
begin
  unfold eval, unfold sort,
  apply list.prod_eq_of_perm,
  apply list.perm_map,
  apply list.perm.symm,
  apply list.perm_merge_sort
end

end pterm

namespace nterm

def to_pterm : @nterm γ _ → @pterm γ _
| (mul x y) := x.to_pterm ++ y.to_pterm
| (pow x n) := x.to_pterm.pow n
| x := ⟨[⟨x, 1⟩]⟩

theorem eval_to_pterm {x : @nterm γ _} :
  nterm.eval ρ x = pterm.eval ρ x.to_pterm :=
begin
  induction x with i c x y ihx ihy x y ihx ihy x n ihx,
  { simp [to_pterm, nterm.eval, pterm.eval, xterm.eval] },
  { simp [to_pterm, nterm.eval, pterm.eval, xterm.eval] },
  { simp [to_pterm, nterm.eval, pterm.eval, xterm.eval] },
  { unfold to_pterm, unfold eval,
    rw [pterm.eval_mul, ihx, ihy] },
  { unfold to_pterm, unfold eval,
    rw [pterm.eval_pow, ihx] }

end

def norm (x : @nterm γ _) : @nterm γ _ :=
x.to_pterm.sort.reduce.to_nterm

theorem correctness {x : @nterm γ _} :
  x.eval ρ = x.norm.eval ρ :=
calc
  x.eval ρ = pterm.eval ρ x.to_pterm             : eval_to_pterm
       ... = pterm.eval ρ x.to_pterm.sort        : pterm.eval_sort
       ... = pterm.eval ρ x.to_pterm.sort.reduce : pterm.eval_reduce
       ... = nterm.eval ρ x.norm                 : pterm.eval_to_nterm

end nterm

end polya
