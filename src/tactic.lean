import .blackboard .sum_form .proof_reconstruction 

open tactic

namespace polya

meta def polya_tactic := state_t blackboard tactic
meta instance pmt : monad polya_tactic := state_t.monad
meta instance pms : monad_state blackboard polya_tactic := state_t.monad_state
meta instance pma : alternative polya_tactic := state_t.alternative

meta def expr_to_ineq : expr → tactic (expr × expr × ineq)
| `(%%x ≤ %%c * %%y) := do c' ← eval_expr rat c, return $ (x, y, ineq.of_comp_and_slope comp.le (slope.some c'))
| `(%%x < %%c * %%y) := do c' ← eval_expr rat c, return $ (x, y, ineq.of_comp_and_slope comp.lt (slope.some c'))
| `(%%x ≥ %%c * %%y) := do c' ← eval_expr rat c, return $ (x, y, ineq.of_comp_and_slope comp.ge (slope.some c'))
| `(%%x > %%c * %%y) := do c' ← eval_expr rat c, return $ (x, y, ineq.of_comp_and_slope comp.gt (slope.some c'))
| _ := failed

meta def expr_to_eq : expr → tactic (expr × expr × ℚ)
| `(%%x = %%c * %%y) := do c' ← eval_expr rat c, return $ (x, y, c')
| _ := fail "mistake in expr_to_eq!"

open gen_comp
-- this fails on = and ≠ right now
meta def expr_to_sign : expr → tactic (expr × gen_comp)
/-| `(@has_lt.lt %%a %%_ %%x (@has_zero.zero _ _)) := return (x, lt)
| `(%%x ≤ 0) := return (x, le)
| `(%%x > 0) := return (x, gt)
| `(%%x ≥ 0) := return (x, ge)
| `(%%x = 0) := return (x, eq)
| `(%%x ≠ 0) := return (x, ne)
| _ := failed-/
:= λ e, do
[_, _, lhs, rhs] ← return e.get_app_args,
if rhs.is_app_of `has_zero.zero then
  if e.is_app_of `has_lt.lt then return (lhs, lt)
  else if e.is_app_of `has_le.le then return (lhs, le)
  else if e.is_app_of `gt then return (lhs, gt)
  else if e.is_app_of `ge then return (lhs, ge)
  else if e.is_app_of `_root_.eq then return (lhs, eq)
  else if e.is_app_of `not then do (e, gc) ← expr_to_sign e.app_arg, return (e, gc.reverse)
  else failed
else failed


meta instance has_coe_tac {α} : has_coe (tactic α) (polya_tactic α) :=
⟨state_t.lift⟩

meta instance has_coe_bb {α} : has_coe (polya_state α) (polya_tactic α) :=
⟨λ f, get >>= (λ bb, let (x, bb') := f.run bb in return x)⟩

meta def add_comp_to_blackboard (e : expr) : polya_tactic unit :=
(do (x, y, ie1) ← expr_to_ineq e, 
    id ← return $ ineq_data.mk ie1 (ineq_proof.hyp x y _ e),
    add_ineq id)
<|>
(do (x, y, ie1) ← expr_to_eq e,
    id ← return $ eq_data.mk ie1 (eq_proof.hyp x y _ e),
    add_eq id)
<|>
(do (x, gc) ← expr_to_sign e,
    sd ← return $ sign_data.mk gc (sign_proof.hyp x _ e),
    add_sign sd)

meta def trace_comps (x y : expr) : polya_tactic unit :=
do id ← get_ineqs x y, trace id

meta def test_cmd {α} (t : polya_tactic α) : tactic α :=
do (b, _) ← t.run (blackboard.mk_empty), return b

--variables x y z w : ℚ
def x : ℚ := 0
def y : ℚ := 0
def z : ℚ := 0
def w : ℚ := 0

run_cmd test_cmd $ 
do (x', y', ie) ← expr_to_ineq `(x > 4*y),
   (x', y', ei) ← expr_to_eq `(x = 3*y),
   ed ← return $ eq_data.mk ei (eq_proof.hyp x' y' _ x'),
   id ← return $ ineq_data.mk ie (ineq_proof.hyp x' y' _ x'),
   trace id.inq.to_slope, trace ed.c, trace id.inq.to_comp,
   trace $ ed.get_implied_sign_info_from_ineq id,
   skip


meta def trace_contr_found : polya_tactic unit :=
do b ← contr_found,
   trace ("contr?", b)

open ineq_info

meta def get_sum_comp_list_of_list (l : list (Σ lhs rhs, ineq_data lhs rhs)) : list sum_form_comp_data :=
l.map (λ ⟨_, _, id⟩, sum_form_comp_data.of_ineq_data id)


run_cmd test_cmd $ 
do add_comp_to_blackboard `(x ≤ 2*y),
   add_comp_to_blackboard `(y < 5*z),
   l ← get_ineq_list,
   trace l,
   sfc_list ← return $ get_sum_comp_list_of_list l,
   exprs ← get_expr_list,
   trace exprs,
   ts ← return $ elim_expr_from_comp_data_list sfc_list (exprs.head),
   trace ts,
   trace $ ts.map sum_form_comp_data.to_ineq_data



run_cmd test_cmd $ 
do add_comp_to_blackboard `(x ≤ 2*y),
   add_comp_to_blackboard `(y < 5*z),
--   add_comp_to_blackboard `(x < 4*y),
--   add_comp_to_blackboard `(y ≥ 1*x),
--   add_comp_to_blackboard `(z ≤ 0*x),
--   add_comp_to_blackboard `(z ≤ -2*y),
--   add_comp_to_blackboard `(x > 0),
--   add_comp_to_blackboard `(y > 0),
   a ← return `(x), b ← return `(y),
   --trace_comps a b
   l ← get_ineq_list,
   sfc_list ← return $ get_sum_comp_list_of_list l,
   exprs ← get_expr_list,
   ts ← return $ elim_expr_from_comp_data_list sfc_list (exprs.head),
   trace ts,
   trace $ ts.map sum_form_comp_data.to_ineq_data

run_cmd test_cmd $ 
do add_comp_to_blackboard `(x ≤ 2*y),
   add_comp_to_blackboard `(x < 4*y),
   a ← return `(x), b ← return `(y),
   si ← get_sign_info a,
   trace si,
   si ← get_sign_info b,
   trace si,
   trace_contr_found,
/-   (x', y', ei) ← expr_to_eq `(x = 3*y),
   ed ← return $ eq_data.mk ei (eq_proof.hyp a b _ x'),
   id ← get_ineqs a b,
   match id with
   | two_comps id1 id2 := do add_implied_signs_from_eq_and_ineq ed id1, trace "!", trace_contr_found
   | _ := trace_contr_found
   end-/
   add_comp_to_blackboard `(x = 3*y),
   trace_comps a b,
   si ← get_sign_info a,
   trace si,
   si ← get_sign_info b,
   trace si,
   b ← contr_found,
   trace ("contr?", b),
   ctd ← get_contr,
   trace ctd

end polya
