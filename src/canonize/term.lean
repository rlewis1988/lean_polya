import data.real.basic --data.list.alist data.finmap

section
local attribute [semireducible] reflected
meta instance rat.reflect : has_reflect ℚ
| ⟨n, d, _, _⟩ := `(rat.mk_nat %%(reflect n) %%(reflect d))
end

@[derive decidable_eq, derive has_reflect]
inductive term : Type
| zero : term
| one : term
| atm : ℕ → term
| add : term → term → term
| mul : term → term → term
| sca : term → ℚ → term
| exp : term → ℤ → term

namespace term

private def str : term → string
| zero := "zero"
| one  := "one"
| (atm i) := "(atm " ++ to_string i ++ ")"
| (add x y) := "(add " ++ str x ++ " " ++ str y ++ ")"
| (mul x y) := "(mul " ++ str x ++ " " ++ str y ++ ")"
| (sca x c) := "(sca " ++ str x ++ " " ++ to_string c ++ ")"
| (exp x n) := "(sca " ++ str x ++ " " ++ to_string n ++ ")"

instance : has_to_string term := ⟨str⟩
meta instance : has_to_format term := ⟨λ t, str t⟩
meta instance : has_to_tactic_format term := ⟨λ t, return (str t)⟩

private def blt : term → term → bool
| zero       zero       := ff
| _          zero       := ff
| zero       _          := tt
| one        one        := ff
| _          one        := ff
| one        _          := tt
| (atm i)    (atm j)    := i < j
| _          (atm _)    := ff
| (atm _)    _          := tt
| (add x x') (add y y') := blt x y ∨ (x = y ∧ blt x' y')
| _          (add _ _)  := ff
| (add _ _)  _          := tt
| (mul x x') (mul y y') := blt x y ∨ (x = y ∧ blt x' y')
| _          (mul _ _)  := ff
| (mul _ _)  _          := tt
| (sca x a)  (sca y b)  := blt x y ∨ (x = y ∧ a < b)
| _          (sca _ _)  := ff
| (sca _ _)  _          := tt
| (exp x n)  (exp y m)  := blt x y ∨ (x = y ∧ n < m)

def lt : term → term → Prop :=
λ x y, blt x y

instance : has_lt term := ⟨lt⟩
instance : decidable_rel lt := by delta lt; apply_instance

-- dictionary for the atoms
structure dict (α : Type*) := (map : ℕ → α)
variables {α : Type*} [discrete_field α]

def eval_term (d : dict α) : term → α
| zero := 0
| one := 1
| (atm i) := d.map i
| (add x y) := eval_term x + eval_term y
| (mul x y) := eval_term x * eval_term y
| (sca x c) := eval_term x * c
| (exp x n) := eval_term x ^ n

instance : has_coe_to_fun (dict α) := ⟨λ _, term → α, eval_term⟩

section
variable {eval : dict α}
variables {x y : term} {i : ℕ} {c : ℚ} {n : ℤ}
@[simp] lemma eval_zero : eval zero = 0 := rfl
@[simp] lemma eval_one : eval one = 1 := rfl
@[simp] lemma eval_atm : eval (atm i) = eval.map i := rfl
@[simp] lemma eval_add : eval (add x y) = eval x + eval y := rfl
@[simp] lemma eval_mul : eval (mul x y) = eval x * eval y := rfl
@[simp] lemma eval_sca : eval (sca x c) = eval x * c := rfl
@[simp] lemma simp_exp : eval (exp x n) = eval x ^ n := rfl
end

section
variable {eval : dict α}
variables (x y z : term) (i : ℕ) (c : ℚ) (n : ℤ)
theorem mul_zero : eval (sca x 0) = 0 := by simp
theorem add_comm : eval (add x y) = eval (add y x) := add_comm _ _
/- TODO: a lot of lemmas -/
end

--TODO: find a name
def foo (eval : dict α) (x y : term) : Type :=
{cs : list term // (∀ c ∈ cs, eval c ≠ 0) → eval x = eval y}

namespace foo

variable {eval : dict α}
variables {x y z : term}

def of_eq (h : eval x = eval y) : foo eval x y :=
⟨[], λ _, h⟩

def rfl : foo eval x x := of_eq (congr_arg _ rfl)

def trans (u : foo eval x y) (v : foo eval y z) : foo eval x z :=
⟨list.union u.val v.val,
    assume H, eq.trans
    (u.property $ assume c hc, H _ (list.mem_union_left hc _))
    (v.property $ assume c hc, H _ (list.mem_union_right _ hc))
⟩

end foo

def step (eval : dict α) : Type := Π (x : term), Σ (y : term), foo eval x y

namespace step

def comp {eval : dict α} (f g : step eval) : step eval :=
assume x : term,
let ⟨y, pr1⟩ := g x in
let ⟨z, pr2⟩ := f y in
⟨z, foo.trans pr1 pr2⟩

infixr ` ∘ ` := comp

end step

variable {eval : dict α}
def f : step eval := sorry
def g : step eval := sorry

def canonize : step eval := f ∘ g

end term

namespace list

def to_dict {α} [inhabited α] (l : list α) : term.dict α :=
⟨λ i, list.func.get i l⟩

open tactic

meta def expr_reflect (type : expr) : list expr → tactic expr
| [] := to_expr ``([] : list %%type)
| (h::t) := do e ← expr_reflect t, to_expr ``(list.cons (%%h : %%type) %%e)

end list

meta def cache_ty := ℕ × list expr
meta def state_dict : Type → Type := state cache_ty

meta def cache_ty.mk : cache_ty := (0, [])

namespace state_dict
meta instance : monad state_dict := state_t.monad 
meta instance : monad_state cache_ty state_dict := state_t.monad_state

meta def add_atom (e : expr) : state_dict ℕ :=
do
    (i, acc) ← get,
    let i : ℕ := list.length acc,
    put (i+1, e::acc),
    return i

end state_dict

namespace tactic
open term native state_dict

private meta def to_term_aux : expr → state_dict term
| `(0) := return zero 
| `(1) := return one
| `(%%a + %%b) := do
    x ← to_term_aux a,
    y ← to_term_aux b,
    return (add x y)
| `(%%a * %%b) := do
    x ← to_term_aux a,
    y ← to_term_aux b,
    return (mul x y)
| e := do
    i ← add_atom e,
    return (atm i)

meta def term_of_expr (e : expr) : tactic (term × expr) :=
do
    let (t, (i, acc)) := (to_term_aux e).run cache_ty.mk,
    atoms ← acc.expr_reflect `(ℝ),
    dict ← mk_app `list.to_dict [atoms],
    p ← to_expr ``(%%e = (%%dict : term → ℝ) %%(reflect t)),
    return (t, p)

end tactic

open tactic
meta def test (e : expr) : tactic unit :=
do
    (t, hyp) ← term_of_expr e,
    trace t,
    ((), pr) ← solve_aux hyp `[simp],
    infer_type pr >>= trace

constants x y z : ℝ

set_option profiler true
run_cmd test `(x * y + 1 * z + 0)
