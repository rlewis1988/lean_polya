import .term

def list.to_dict {α} [inhabited α] (l : list α) : dict α :=
⟨λ i, list.func.get i l.reverse⟩
--TODO: more efficient implementatio

meta def cache_ty := ℕ × list expr
meta def cache_ty.mk : cache_ty := (0, [])

meta def state_dict : Type → Type := state cache_ty

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
namespace term
open tactic polya.state_dict

private meta def of_expr_aux : expr → state_dict term
| `(0 : ℝ) := return zero 
| `(1 : ℝ) := return one
| `(%%a + %%b) := do
    x ← of_expr_aux a,
    y ← of_expr_aux b,
    return (add x y)
| `(%%a * %%b) := do
    x ← of_expr_aux a,
    y ← of_expr_aux b,
    return (mul x y)
| e := do
    i ← add_atom e,
    return (atm i)
--TODO: other patterns

meta def of_expr (e : expr) : tactic (term × expr) :=
do
    let (t, (i, acc)) := (of_expr_aux e).run cache_ty.mk,
    atoms ← acc.expr_reflect `(ℝ),
    dict ← mk_app ``list.to_dict [atoms],
    p ← to_expr ``(%%e = (%%dict).eval %%(reflect t)),
    return (t, p)

meta def test (e : expr) : tactic unit :=
do
    (t, hyp) ← term.of_expr e,
    ((), pr) ← solve_aux hyp `[refl; done],
    infer_type pr >>= trace

end term
end tactic

constants x y z : ℝ

set_option trace.app_builder true
run_cmd tactic.term.test `(x*y + z*1 + y*0)

end polya