import .sterm .pterm

namespace polya

inductive alt {γ} [const_space γ] : Type
| sform : list (@nterm γ _) → @sterm γ _ → alt
| pform : list (@nterm γ _) → @pterm γ _ → alt

namespace alt
open nterm

variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

def singleton (x : @nterm γ _) : @alt γ _ :=
sform [] (sterm.singleton x)

def to_nterm : @alt γ _ → @nterm γ _
| (sform _ S) := S.to_nterm
| (pform _ P) := P.to_nterm

def hyps : @alt γ _ → list (@nterm γ _)
| (sform l _) := l
| (pform l _) := l

def eval (ρ : dict α) (x : @alt γ _) : α :=
nterm.eval ρ x.to_nterm

theorem eval_def {x : @alt γ _} : eval ρ x = nterm.eval ρ x.to_nterm := rfl

def reduce : @alt γ _ → @alt γ _
| (sform l S) := sform l S.reduce
| (pform l P) := pform (l ∪ P.reduce_hyps) P.reduce

def reduce_hyps : @alt γ _ → list (@nterm γ _)
| (sform l S) := []
| (pform l P) := P.reduce_hyps

def to_sterm : @alt γ _ → @sterm γ _
| (sform _ S) := S
| x := sterm.of_nterm x.to_nterm

def to_pterm : @alt γ _ → @pterm γ _
| (pform _ P) := P
| x := pterm.of_nterm x.to_nterm

theorem eval_singleton {x : @nterm γ _} :
  eval ρ (singleton x) = nterm.eval ρ x :=
begin
  unfold singleton, unfold eval, unfold to_nterm,
  rw [← sterm.eval_to_nterm, sterm.eval_singleton]
end

theorem eval_reduce {x : @alt γ _} :
  nonzero ρ x.reduce_hyps →
  eval ρ x.reduce = eval ρ x :=
begin
  intro H,
  cases x with l S l P,
  { unfold reduce, unfold eval, unfold to_nterm,
    rw [← sterm.eval_to_nterm, ← sterm.eval_reduce, sterm.eval_to_nterm] },
  { unfold reduce, unfold eval, unfold to_nterm,
    rw [← pterm.eval_to_nterm, ← pterm.eval_reduce H, pterm.eval_to_nterm] }
end

theorem eval_to_sterm {x : @alt γ _} :
  eval ρ x = sterm.eval ρ x.to_sterm :=
begin
  cases x,
  { unfold to_sterm, unfold eval, unfold to_nterm, rw ← sterm.eval_to_nterm },
  { unfold to_sterm, unfold eval, unfold to_nterm, rw ← sterm.eval_of_nterm }
end

theorem eval_to_pterm {x : @alt γ _} :
  eval ρ x = pterm.eval ρ x.to_pterm :=
begin
  cases x,
  { unfold to_pterm, unfold eval, unfold to_nterm, rw ← pterm.eval_of_nterm },
  { unfold to_pterm, unfold eval, unfold to_nterm, rw ← pterm.eval_to_nterm }
end

def add (x y : @alt γ _) : @alt γ _ :=
sform (x.hyps ∪ y.hyps) (x.to_sterm + y.to_sterm)
--TODO: more cases to avoid switching form too often

def mul (x y : @alt γ _) : @alt γ _ :=
pform (x.hyps ∪ y.hyps) (x.to_pterm * y.to_pterm)
--TODO: more cases to avoid switching form too often

def pow (x : @alt γ _) (n : znum) : @alt γ _ :=
if n = 0 then singleton (1 : γ)
else if n = 1 then x
else pform x.hyps (x.to_pterm ^ n)

instance : has_add (@alt γ _) := ⟨add⟩
instance : has_mul (@alt γ _) := ⟨mul⟩
instance : has_pow (@alt γ _) znum := ⟨pow⟩

@[simp] theorem hyps_add {x y : @alt γ _} :
  (x + y).hyps = x.hyps ∪ y.hyps :=
by { simp [hyps, has_add.add, add] }

@[simp] theorem hyps_mul {x y : @alt γ _} :
  (x * y).hyps = x.hyps ∪ y.hyps :=
by { simp [hyps, has_mul.mul, mul] }

@[simp] theorem hyps_pow {x : @alt γ _} {n : znum} :
  (x ^ n).hyps = if n = 0 then [] else x.hyps :=
begin
  by_cases h0 : n = 0;
  by_cases h1 : n = 1;
  simp [h0, h1, has_pow.pow, pow, hyps, singleton]
end

def of_nterm : @nterm γ _ → @alt γ _
| (nterm.add x y) := of_nterm x + of_nterm y
| (nterm.mul x y) := of_nterm x * of_nterm y
| (nterm.pow x n) := of_nterm x ^ n
| x := singleton x

theorem eval_of_nterm {x : @nterm γ _} :
  nonzero ρ (of_nterm x).hyps →
  eval ρ (of_nterm x) = nterm.eval ρ x :=
begin
  induction x with i c x y ihx ihy x y ihx ihy x n ihx,
  { intro, unfold of_nterm, rw eval_singleton },
  { intro, unfold of_nterm, rw eval_singleton },
  repeat {sorry}
end

end alt

namespace nterm

variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

def norm (x : @nterm γ _) : @nterm γ _ :=
(alt.of_nterm x).to_nterm

def norm_hyps (x : @nterm γ _) : list (@nterm γ _) :=
(alt.of_nterm x).hyps

def correctness {x : @nterm γ _} :
  nonzero ρ (norm_hyps x) →
  nterm.eval ρ x = nterm.eval ρ (norm x) :=
begin
  sorry
end

def naive_norm : @nterm γ _ → @nterm γ _
| (add x y) := (sterm.of_nterm (naive_norm x) + sterm.of_nterm (naive_norm y)).reduce.to_nterm
| (mul x y) := (pterm.of_nterm (naive_norm x) * pterm.of_nterm (naive_norm y)).reduce.to_nterm
| (pow x n) := (pterm.of_nterm (naive_norm x) ^ n).reduce.to_nterm
| x := x

theorem soundness {x : @nterm γ _} :
  norm x = naive_norm x :=
begin
  sorry
end

end nterm

end polya
