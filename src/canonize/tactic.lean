import data.list.alist data.finmap
import .sterm .pterm

namespace list
open tactic

meta def expr_reflect (type : expr) : list expr → tactic expr
| [] := to_expr ``([] : list %%type)
| (h::t) := do e ← expr_reflect t, to_expr ``(list.cons (%%h : %%type) %%e)

end list

namespace polya

@[derive decidable_eq, derive has_reflect]
inductive eterm {γ} [const_space γ] : Type
| zero  : eterm
| one   : eterm
| const : γ → eterm
| atom  : num → eterm
| add   : eterm → eterm → eterm
| sub   : eterm → eterm → eterm
| mul   : eterm → eterm → eterm
| div   : eterm → eterm → eterm
| neg   : eterm → eterm
| inv   : eterm → eterm
| pow   : eterm → ℤ → eterm

namespace eterm

variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

def eval (ρ : dict α) : @eterm γ _ → α
| zero      := 0
| one       := 1
| (const r) := morph.f _ r
| (atom i)  := ρ.val i
| (add x y) := eval x + eval y
| (sub x y) := eval x - eval y
| (mul x y) := eval x * eval y
| (div x y) := (eval x) / (eval y)
| (neg x)   := - eval x
| (inv x)   := (eval x)⁻¹
| (pow x n) := eval x ^ n

def to_nterm : @eterm γ _ → @nterm γ _
| zero      := 0
| one       := 1
| (const c) := c
| (atom i)  := i
| (add x y) := to_nterm x + to_nterm y
| (sub x y) := to_nterm x - to_nterm y
| (mul x y) := to_nterm x * to_nterm y
| (div x y) := to_nterm x / to_nterm y
| (neg x)   := - to_nterm x
| (inv x)   := to_nterm x ^ (-1 : znum)
| (pow x n) := to_nterm x ^ (n : znum)

theorem correctness {x : @eterm γ _} :
  x.eval ρ = (to_nterm x).eval ρ :=
begin
  induction x with
    c           --const
    i           --atom
    x y ihx ihy --add
    x y ihx ihy --sub
    x y ihx ihy --mul
    x y ihx ihy --div
    x ihx       --neg
    x ihx       --inv
    x n ihx;    --pow
  unfold to_nterm; unfold eterm.eval,
  repeat { simp },
  repeat { simp [ihx] },
  repeat { simp [ihx, ihy] },
  { simp [fpow_inv] }
end

end eterm

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

def naive_norm : @nterm γ _ → @nterm γ _
| (add x y) := (sterm.of_nterm (naive_norm x) + sterm.of_nterm (naive_norm y)).reduce.to_nterm
| (mul x y) := (pterm.of_nterm (naive_norm x) * pterm.of_nterm (naive_norm y)).reduce.to_nterm
| (pow x n) := (pterm.of_nterm (naive_norm x) ^ n).reduce.to_nterm
| x := x

def norm (x : @nterm γ _) : @nterm γ _ := (alt.of_nterm x).to_nterm
def norm_hyps (x : @nterm γ _) : list (@nterm γ _) := (alt.of_nterm x).hyps

theorem soundness {x : @nterm γ _} :
  norm x = naive_norm x :=
by sorry

def correctness {x : @nterm γ _} :
  nonzero ρ (norm_hyps x) →
  nterm.eval ρ x = nterm.eval ρ (norm x) :=
begin
  sorry
end

end nterm

open eterm native tactic

meta structure cache_ty :=
(new_atom : num)
(atoms : rb_map expr num)

meta instance : has_emptyc cache_ty := ⟨⟨0, rb_map.mk _ _⟩⟩

meta def state_dict : Type → Type := state cache_ty

meta instance state_dict_monad : monad state_dict := state_t.monad 
meta instance state_dict_monad_state : monad_state cache_ty state_dict := state_t.monad_state

meta def get_atom (e : expr) : state_dict num :=
get >>= λ s,
match s.atoms.find e with
| (some i) := return i
| none     := do
    let i := s.new_atom,
    put ⟨i + 1, s.atoms.insert e i⟩,
    return i
end

def list_to_dict {α} [inhabited α] (l : list α) : dict α :=
⟨λ i, list.func.get i l⟩


def finmap.to_dict (m : finmap (λ _ : num, ℝ)) : dict ℝ :=
⟨λ i, match finmap.lookup i m with (some x) := x | _ := 0 end⟩

meta def cache_ty.get_dict (s : cache_ty) : tactic expr :=
do
    let l := s.atoms.to_list.merge_sort (λ x y, x.snd ≤ y.snd),
    let l := l.map prod.fst,
    e ← l.expr_reflect `(ℝ),
    mk_app ``list_to_dict [e]

meta def cache_ty.get_f (s : cache_ty) : num → expr :=
do
    let l := s.atoms.to_list.merge_sort (λ x y, x.snd ≤ y.snd) in
    let l := l.map prod.fst in
    λ i, list.func.get i l

@[reducible]
def γ := ℚ

instance : const_space γ :=
{ df := by apply_instance,
  le := by apply_instance, 
  dec_le := by apply_instance,
}

meta def aux_const : expr → option γ
| `(@has_zero.zero %%α %%s)  := some 0
| `(@has_one.one %%α %%s)    := some 1
| `(@bit0 %%α %%s %%v)       := bit0 <$> aux_const v
| `(@bit1 %%α %%s₁ %%s₂ %%v) := bit1 <$> aux_const v
| `(%%a / %%b)               := do
    x ← aux_const a,
    y ← aux_const b,
    return (x / y)
| _                          := none

meta def aux_num : expr → option ℤ
| `(@has_zero.zero %%α %%s)  := some 0
| `(@has_one.one %%α %%s)    := some 1
| `(@bit0 %%α %%s %%v)       := bit0 <$> aux_num v
| `(@bit1 %%α %%s₁ %%s₂ %%v) := bit1 <$> aux_num v
| `(- %%a)                   := has_neg.neg <$> aux_num a
| _                          := none

meta def eterm_of_expr : expr → state_dict (@eterm γ _) | e :=
match e with
| `(0 : ℝ) := return zero
| `(1 : ℝ) := return one
| `(%%a + %%b) := do
    x ← eterm_of_expr a,
    y ← eterm_of_expr b,
    return (add x y)
| `(%%a - %%b) := do
    x ← eterm_of_expr a,
    y ← eterm_of_expr b,
    return (sub x y)
| `(%%a * %%b) := do
    x ← eterm_of_expr a,
    y ← eterm_of_expr b,
    return (mul x y)
| `(%%a / %%b) := do
    x ← eterm_of_expr a,
    y ← eterm_of_expr b,
    return (div x y)
| `(-%%a) := do
    x ← eterm_of_expr a,
    return (neg x)
| `((%%a)⁻¹) := do
    x ← eterm_of_expr a,
    return (inv x)
| `(%%a ^ %%n) :=
    match aux_num n with
    | (some n) := (λ x, pow x n) <$> eterm_of_expr a
    | none     := atom <$> get_atom e
    end
| `(↑%%e) :=
    match aux_const e with
    | (some n) := return (const n)
    | none     := atom <$> get_atom e
    end
| _ := atom <$> get_atom e
end

meta def nterm_to_expr (f : num → expr) : @nterm γ _ → tactic expr
| (nterm.atom i)  := return (f i)
| (nterm.const c) := to_expr ``(%%(reflect c) : ℝ)
| (nterm.add x y) := do
  a ← nterm_to_expr x,
  b ← nterm_to_expr y,
  to_expr ``(%%a + %%b)
| (nterm.mul x y) := do
  a ← nterm_to_expr x,
  b ← nterm_to_expr y,
  to_expr ``(%%a * %%b)
| (nterm.pow x n) := do
  a ← nterm_to_expr x,
  to_expr ``(%%a ^ (%%(reflect n) : ℤ))

def norm (x : @eterm γ _) : @nterm γ _ :=
x.to_nterm.norm

def norm_hyps (x : @eterm γ _) : list (@nterm γ _) :=
x.to_nterm.norm_hyps

theorem correctness {x : @eterm γ _} {ρ : dict ℝ} :
  (∀ t ∈ norm_hyps x, nterm.eval ρ t ≠ 0) →
  eterm.eval ρ x = nterm.eval ρ (norm x) :=
begin
  intro H,
  unfold norm,
  apply eq.trans,
  { apply eterm.correctness },
  { apply nterm.correctness H }
end

meta def norm_expr (e : expr) : tactic (@nterm γ _ × expr × expr) :=
do
  let (t, s) := (eterm_of_expr e).run ∅,
  

  ρ ← s.get_dict,
  let rt : expr := `(t),
  hyp ← to_expr ``(∀ t ∈ norm_hyps %%rt, nterm.eval %%ρ t ≠ 0),

  h1 ← to_expr ``(%%e = eterm.eval %%ρ %%rt),
  ((), pr1) ← solve_aux h1 `[refl; done],
  h2 ← to_expr ``(%%hyp → eterm.eval %%ρ %%rt = nterm.eval %%ρ (norm %%rt)),
  ((), pr2) ← solve_aux h2 `[apply correctness; done],
  
  let nt := norm t,
  new_e ← nterm_to_expr s.get_f (norm t),
  return  (nt, new_e, pr1)

end polya
