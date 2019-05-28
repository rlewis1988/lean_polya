import .nterm

namespace polya

open nterm

variables {α : Type} [discrete_field α]
variables {γ : Type} [coeff γ]
variables [morph γ α] {ρ : dict α}

--@[derive decidable_eq]
structure xterm : Type :=
(term : @nterm γ _)
(exp : znum)

namespace xterm

--TODO: unable to derive decidable_eq
instance decidable_eq : decidable_eq (@xterm γ _) := sorry

def le (x y : @xterm γ _) : Prop := x.term ≤ y.term

instance : has_le (@xterm γ _) := ⟨le⟩
instance : decidable_rel (@xterm.le γ _) := by delta xterm.le; apply_instance

def mul (x : @xterm γ _) (n : znum) : @xterm γ _ :=
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

theorem eval_add' {x : @nterm γ _} {n m : znum} :
  nterm.eval ρ x ≠ 0 → xterm.eval ρ ⟨x, n + m⟩ = xterm.eval ρ ⟨x, n⟩ * xterm.eval ρ ⟨x, m⟩ :=
begin
  intro hx,
  simp [xterm.eval, fpow_add hx]
end

theorem eval_add (x : @nterm γ _) (n m : znum) :
  n + m ≠ 0 → xterm.eval ρ ⟨x, n + m⟩ = xterm.eval ρ ⟨x, n⟩ * xterm.eval ρ ⟨x, m⟩ :=
begin
  intro h1,
  have h2 : n ≠ 0 ∨ m ≠ 0, by { sorry },
  by_cases hx : nterm.eval ρ x = 0,
  { simp only [eval], rw hx,
    apply eq.trans,
    { apply zero_fpow,
      rw ← znum.cast_zero,
      exact_mod_cast h1 },
    { rw zero_eq_mul,
      cases h2,
      { left, apply zero_fpow,
        rw ← znum.cast_zero,
        exact_mod_cast h2 },
      { right, apply zero_fpow,
        rw ← znum.cast_zero,
        exact_mod_cast h2 }}},
  { simp [eval, fpow_add, hx] }
end

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

theorem eval_mul {x : @xterm γ _} {n : znum} :
  (x.mul n).eval ρ = x.eval ρ ^ (n : ℤ) :=
by simp [mul, eval, fpow_mul] 

end xterm

structure pterm : Type :=
(terms : list (@xterm γ _))

namespace pterm

def append (P1 P2 : @pterm γ _) : @pterm γ _ :=
⟨P1.terms ++ P2.terms⟩

instance : has_append (@pterm γ _) := ⟨append⟩

theorem append_terms (P1 P2 : @pterm γ _) :
  (P1 ++ P2).terms = P1.terms ++ P2.terms := rfl

def mul (P : @pterm γ _) (n : znum) : @pterm γ _ :=
if n = 0 then ⟨[]⟩
else if n = 1 then P
else ⟨P.terms.map (λ x, x.mul n)⟩

def eval (ρ : dict α) (P : @pterm γ _) : α :=
list.prod (P.terms.map (xterm.eval ρ))


theorem eval_mul (P : @pterm γ _) (n : znum) :
(P.mul n).eval ρ = P.eval ρ ^ (n : ℤ) :=
begin
  by_cases h : n = 0 ∨ n = 1,
  { cases h with h h,
    { simp [h, mul, eval] },
    { simp [h, mul, eval] }},
  { have h0 : ¬ n = 0, by { intro h0, apply h, left, exact h0 },
    have h1 : ¬ n = 1, by { intro h1, apply h, right, exact h1 },
    cases P with terms,
    simp [h0, h1, mul, eval], 
    induction terms with x xs ih,
    { simp },
    { simp [ih, mul_fpow, xterm.eval_mul] }
  }
end

theorem eval_append (P1 P2 : @pterm γ _) :
  (P1 ++ P2).eval ρ = P1.eval ρ * P2.eval ρ :=
begin
  unfold eval,
  simp only [append_terms],
  rw [list.map_append],
  apply list.prod_append 
end

def to_nterm (P : @pterm γ _) : @nterm γ _ :=
prod (P.terms.map (xterm.to_nterm))

theorem eval_to_nterm {P : @pterm γ _} :
  P.eval ρ = P.to_nterm.eval ρ :=
begin
  cases P with terms,
  unfold to_nterm, unfold eval,
  rw [eval_prod, list.map_map],
  rw xterm.eval_to_nterm'
end

structure reduce_cache : Type :=
(t : @xterm γ _)
(ts : list (@xterm γ _))
(hyps : list (@nterm γ _))

def reduce_cache.eval (ρ : dict α) (pi : @reduce_cache γ _) : α :=
if nterm.eval ρ pi.t.term = 0 then 0
else xterm.eval ρ pi.t * pterm.eval ρ ⟨pi.ts⟩

def reduce_aux : @reduce_cache γ _ → @xterm γ _ → @reduce_cache γ _
| ⟨⟨x, n⟩, ts, hyps⟩ ⟨y, m⟩ :=
  if m = 0 then
    ⟨⟨x, n⟩, ts, hyps⟩
  else if x = y then
    ⟨⟨x, n + m⟩, ts, hyps⟩
  else if n = 0 then
    ⟨⟨y, m⟩, ts, x::hyps⟩
  else
    ⟨⟨y, m⟩, ⟨x, n⟩::ts, hyps⟩

def reduce_ih (ρ : dict α) (c : α) (pi : @reduce_cache γ _) : Prop :=
  (∀ h ∈ pi.hyps, nterm.eval ρ h ≠ 0) → pi.eval ρ = c

theorem eval_reduce_aux (c : α) (y : @xterm γ _)
  (pi : @reduce_cache γ _)
  (ih : reduce_ih ρ c pi) :
  reduce_ih ρ (xterm.eval ρ y * c) (reduce_aux pi y) :=
begin
  cases pi with x xs ts,
  cases x with x n,
  cases y with y m,
  intro H,
  have H' : ∀ t ∈ ts, nterm.eval ρ t ≠ 0,
  by {
    by_cases h1 : m = 0,
    { simp [reduce_aux, h1] at H, apply H },
    { by_cases h2 : x = y,
      { simp [reduce_aux, h1, h2] at H, apply H },
      { by_cases h3 : n = 0,
        { simp [reduce_aux, h1, h2, h3] at H, apply H.right },
        { simp [reduce_aux, h1, h2, h3] at H, apply H }}}},
  have ih' := ih H',
  have hc : nterm.eval ρ x = 0 → c = 0,
  by { intro hx, rw ← ih H', simp [reduce_cache.eval, hx] },
  
  by_cases h1 : m = 0,
  { simp [reduce_aux, xterm.eval, h1, ih H'] },
  by_cases hy : nterm.eval ρ y = 0,
  { have : (0 : α) ^ (m : ℤ) = 0,
    by { apply zero_fpow, rw ← znum.cast_zero, exact_mod_cast h1 },
    by_cases h2 : x = y; by_cases h3 : n = 0;
    simp [reduce_aux, reduce_cache.eval, xterm.eval, h1, h2, h3, hy, this] },
  by_cases h2 : x = y,
  { have hx : nterm.eval ρ x ≠ 0, by rw h2; exact hy,
    suffices : xterm.eval ρ ⟨y, n + m⟩ * pterm.eval ρ ⟨xs⟩ = xterm.eval ρ ⟨y, m⟩ * c,
    by simp [reduce_aux, reduce_cache.eval, h1, h2, hy, this],
    calc
    xterm.eval ρ ⟨y, n + m⟩ * pterm.eval ρ ⟨xs⟩
        = xterm.eval ρ ⟨y, n⟩ * xterm.eval ρ ⟨y, m⟩ * pterm.eval ρ ⟨xs⟩ : by rw xterm.eval_add' hy
    ... = xterm.eval ρ ⟨y, m⟩ * (xterm.eval ρ ⟨y, n⟩ * pterm.eval ρ ⟨xs⟩) : by ring
    ... = xterm.eval ρ ⟨y, m⟩ * c : by { rw ← ih H', rw ← h2, simp [reduce_cache.eval, hx] }
  },
  by_cases h3 : n = 0,
  { have h3' : (n : ℤ) = 0, by { rw ← znum.cast_zero, exact_mod_cast h3 },
    suffices : xterm.eval ρ ⟨y, m⟩ * pterm.eval ρ ⟨xs⟩ = xterm.eval ρ ⟨y, m⟩ * c,
    by simp [reduce_aux, reduce_cache.eval, h1, h2, h3, hy, this],
    have hx : nterm.eval ρ x ≠ 0,
    by { apply H, simp [reduce_aux, h1, h2, h3] },
    simp [reduce_cache.eval, xterm.eval, hx, h3] at ih',
    rw ih' },
  have h3' : (n : ℤ) ≠ 0, by { rw ← znum.cast_zero, exact_mod_cast h3 },
  by_cases hx : nterm.eval ρ x = 0,
  { simp [reduce_aux, reduce_cache.eval, xterm.eval, pterm.eval, h1, h2, h3, hy, hx, hc, zero_fpow, h3'] },
  simp [reduce_cache.eval, xterm.eval, hx] at ih',
  rw ← ih',
  simp [reduce_aux, h1, h2, h3, reduce_cache.eval, hx, xterm.eval, hy, pterm.eval]

end

def reduce (P : @pterm γ _) : list (@nterm γ _) × @pterm γ _ :=
match P.terms with
| []      := ([], ⟨[]⟩)
| (x::xs) :=
  let pi := list.foldl reduce_aux ⟨x, [], []⟩ xs in
  if pi.t.exp = 0 then
    (pi.t.term::pi.hyps, ⟨xs⟩)
  else
    (pi.hyps, ⟨x::xs⟩)
end

theorem eval_reduce {P : @pterm γ _} :
  (∀ t ∈ P.reduce.fst, nterm.eval ρ t ≠ 0) → P.eval ρ = P.reduce.snd.eval ρ :=
by sorry

def sort (P : @pterm γ _) : @pterm γ _ :=
⟨P.terms.merge_sort (≤)⟩

theorem eval_sort {P : @pterm γ _} :
  P.eval ρ = P.sort.eval ρ :=
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
| (pow x n) := x.to_pterm.mul n
| x := ⟨[⟨x, 1⟩]⟩

theorem eval_to_pterm {x : @nterm γ _} :
  nterm.eval ρ x = pterm.eval ρ x.to_pterm :=
begin
  induction x with i c x y ihx ihy x y ihx ihy x n ihx,
  { simp [to_pterm, nterm.eval, pterm.eval, xterm.eval] },
  { simp [to_pterm, nterm.eval, pterm.eval, xterm.eval] },
  { simp [to_pterm, nterm.eval, pterm.eval, xterm.eval] },
  { unfold to_pterm, unfold eval,
    rw [pterm.eval_append, ihx, ihy] },
  { unfold to_pterm, unfold eval,
    rw [pterm.eval_mul, ihx] }

end

def norm (x : @nterm γ _) : list (@nterm γ _) × @nterm γ _ :=
let pi := x.to_pterm.sort.reduce in
(pi.fst, pi.snd.to_nterm)

theorem correctness {x : @nterm γ _} :
  (∀ t ∈ x.norm.fst, nterm.eval ρ t ≠ 0) → x.eval ρ = x.norm.snd.eval ρ :=
assume h,
calc
  x.eval ρ = pterm.eval ρ x.to_pterm                 : eval_to_pterm
       ... = pterm.eval ρ x.to_pterm.sort            : pterm.eval_sort
       ... = pterm.eval ρ x.to_pterm.sort.reduce.snd : pterm.eval_reduce h
       ... = nterm.eval ρ x.norm.snd                 : pterm.eval_to_nterm

end nterm

end polya
