import .datatypes
open polya tactic

meta def expr_to_ineq : expr → tactic ineq
| ```(%%x ≤ %%c*%%y) := do c' ← eval_expr rat c, return $ ineq.of_comp_and_slope comp.le (slope.some c')
| ```(%%x < %%c*%%y) := do c' ← eval_expr rat c, return $ ineq.of_comp_and_slope comp.lt (slope.some c')
| ```(%%x ≥ %%c*%%y) := do c' ← eval_expr rat c, return $ ineq.of_comp_and_slope comp.ge (slope.some c')
| ```(%%x > %%c*%%y) := do c' ← eval_expr rat c, return $ ineq.of_comp_and_slope comp.gt (slope.some c')
| _ := failed

variables x y : ℚ
include x y

example : true := by do
x ← get_local `x, y ← get_local `y,
e1 ← to_expr `(x < 1*y),
e2 ← to_expr `(x ≥ 2*y),
e3 ← to_expr `(x ≤ 1*y),
ie1 ← expr_to_ineq e1,
ie2 ← expr_to_ineq e2,
ie3 ← expr_to_ineq e3,
trace ie1, trace ie2, trace ie3, 
id1 ← return $ ineq_data.mk ie1 (ineq_proof.hyp x y _ e1),
id2 ← return $ ineq_data.mk ie2 (ineq_proof.hyp x y _ e1),
id3 ← return $ ineq_data.mk ie3 (ineq_proof.hyp x y _ e1),
ii ← return $ ineq_info.two_comps id1 id2,
trace $ ii.implies id3,
triv

#exit
ie2 ← expr_to_ineq ```(x ≤ 2*y),
failed

variables x y : ℚ
run_cmd expr_to_ineq ```(x ≤ 2/3*y) >>= tactic.trace
