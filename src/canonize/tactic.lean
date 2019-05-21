import .term data.list.alist data.finmap

namespace polya
open term tactic
open native

meta structure cache_ty :=
(new_atom : num)
(atoms : rb_map expr num)
(val : tactic expr)

private meta def empty_val : tactic expr :=
to_expr ``([] : list ℝ)
--to_expr ``(@has_emptyc.emptyc (finmap (λ _ : ℕ, ℝ)) _)
meta instance : has_emptyc cache_ty := ⟨⟨0, rb_map.mk _ _, empty_val⟩⟩

meta def state_dict : Type → Type := state cache_ty

meta instance state_dict_monad : monad state_dict := state_t.monad 
meta instance state_dict_monad_state : monad_state cache_ty state_dict := state_t.monad_state

meta def insert_val (k : ℕ) (e : expr) (m : expr) : tactic expr :=
do
mk_app `list.cons [e, m]
--mk_app `finmap.insert [reflect k, e, m]

meta def get_atom (e : expr) : state_dict num :=
get >>= λ s,
match s.atoms.find e with
| (some i) := return i
| none     := do
    let i := s.new_atom,
    put ⟨i + 1, s.atoms.insert e i, s.val >>= insert_val i e⟩,
    return i
end

def list.to_dict {α} [inhabited α] (l : list α) : dict α :=
⟨λ i, list.func.get i l.reverse⟩
--TODO: more efficient implementation

def finmap.to_dict (m : finmap (λ _ : ℕ, ℝ)) : dict ℝ :=
⟨λ i, match finmap.lookup i m with (some x) := x | _ := 0 end⟩

meta def cache_ty.get_dict (s : cache_ty) : tactic expr :=
do
    m ← s.val,
    mk_app ``list.to_dict [m]
    --mk_app ``finmap.to_dict [m]

@[reducible]
def γ := ℚ

meta def aux_const : expr → option γ
| `(@has_zero.zero %%α %%s)  := some 0
| `(@has_one.one %%α %%s)    := some 1
| `(@bit0 %%α %%s %%v)       := bit0 <$> aux_const v
| `(@bit1 %%α %%s₁ %%s₂ %%v) := bit1 <$> aux_const v
| _                          := none
--TODO: add fractions

meta def aux_num : expr → option ℤ
| `(@has_zero.zero %%α %%s)  := some 0
| `(@has_one.one %%α %%s)    := some 1
| `(@bit0 %%α %%s %%v)       := bit0 <$> aux_num v
| `(@bit1 %%α %%s₁ %%s₂ %%v) := bit1 <$> aux_num v
| `(- %%a)                   := has_neg.neg <$> aux_num a
| _                          := none

meta def term_of_expr : expr → state_dict (@term γ _) | e :=
    match e with
    | `(0 : ℝ) := return zero 
    | `(1 : ℝ) := return one
    | `(%%a + %%b) := do
        x ← term_of_expr a,
        y ← term_of_expr b,
        return (add x y)
    | `(%%a - %%b) := do
        x ← term_of_expr a,
        y ← term_of_expr b,
        return (sub x y)
    | `(%%a * %%b) := do
        x ← term_of_expr a,
        y ← term_of_expr b,
        return (mul x y)
    | `(%%a / %%b) := do
        x ← term_of_expr a,
        y ← term_of_expr b,
        return (div x y)
    | `(-%%a) := do
        x ← term_of_expr a,
        return (neg x)
    | `((%%a)⁻¹) := do
        x ← term_of_expr a,
        return (inv x)
    | `(%%a ^ %%n) :=
        match aux_num n with
        | (some n) := (λ x, term.pow x n) <$> term_of_expr a 
        | none := atom <$> get_atom e
        end
    | `(↑%%e) :=
        match aux_const e with
        | (some n) := return (const n)
        | none := atom <$> get_atom e
        end
    | _ := atom <$> get_atom e
    end

meta def nterm_of_expr (e : expr) : tactic (@nterm γ _ × expr) :=
do
    let (t, s) := (term_of_expr e).run ∅,
    let nt := nterm.of_term t,
    ρ ← s.get_dict,
    
    h1 ← to_expr ``(%%e = term.eval %%ρ %%(reflect t)),
    h2 ← to_expr ``(term.eval %%ρ %%(reflect t) = nterm.eval %%ρ %%(reflect nt)),
    ((), pr1) ← solve_aux h1 `[refl; done],
    ((), pr2) ← solve_aux h2 `[apply nterm.correctness; done],

    pr ← mk_eq_trans pr1 pr2,
    return (nt, pr)

end polya
