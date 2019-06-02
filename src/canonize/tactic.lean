import data.list.alist data.finmap
import .norm

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
  nterm.eval ρ (to_nterm x) = eval ρ x :=
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
--TODO: replace with Qnum

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

def norm (x : @eterm γ _) : @nterm γ _ :=
x.to_nterm.norm

def norm_hyps (x : @eterm γ _) : list (@nterm γ _) :=
x.to_nterm.norm_hyps

theorem correctness {x : @eterm γ _} {ρ : dict ℝ} :
  (∀ t ∈ norm_hyps x, nterm.eval ρ t ≠ 0) →
  nterm.eval ρ (norm x) = eterm.eval ρ x :=
begin
  intro H,
  unfold norm,
  apply eq.trans,
  { apply nterm.correctness, apply H },
  { apply eterm.correctness }
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

meta def test_norm (e : expr) : tactic (expr × expr × list expr) :=
do
  let (t, s) := (eterm_of_expr e).run ∅,
  naive_new_e ← nterm_to_expr s.get_f t.to_nterm.naive_norm,
  new_e ← nterm_to_expr s.get_f t.to_nterm.norm,
  hyps ← monad.mapm (nterm_to_expr s.get_f) t.to_nterm.norm_hyps,
  return  (naive_new_e, new_e, hyps)

--output expressions for:
--the term produced by the naive norm function
--the term produced by the norm function, which should be the same
--the terms assumed to be nonzero

end polya
