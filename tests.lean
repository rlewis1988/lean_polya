import .datatypes .blackboard
open polya tactic

meta def expr_to_ineq : expr → tactic (expr × expr × ineq)
| ```(%%x ≤ %%c*%%y) := do c' ← eval_expr rat c, return $ (x, y, ineq.of_comp_and_slope comp.le (slope.some c'))
| ```(%%x < %%c*%%y) := do c' ← eval_expr rat c, return $ (x, y, ineq.of_comp_and_slope comp.lt (slope.some c'))
| ```(%%x ≥ %%c*%%y) := do c' ← eval_expr rat c, return $ (x, y, ineq.of_comp_and_slope comp.ge (slope.some c'))
| ```(%%x > %%c*%%y) := do c' ← eval_expr rat c, return $ (x, y, ineq.of_comp_and_slope comp.gt (slope.some c'))
| _ := failed

meta def test_ineqs_imply (e1 e2 n : expr) (output : bool) : tactic unit :=
do (x, y, ie1) ← expr_to_ineq e1,
   (_, _, ie2) ← expr_to_ineq e2,
   (_, _, ien) ← expr_to_ineq n,
   id1 ← return $ ineq_data.mk ie1 (ineq_proof.hyp x y _ e1),
   id2 ← return $ ineq_data.mk ie2 (ineq_proof.hyp x y _ e1),
   id3 ← return $ ineq_data.mk ien (ineq_proof.hyp x y _ e1),
   /-trace ("id1", id1.inq.x, id1.inq.y),
   trace ("id2", id2.inq.x, id2.inq.y),
   trace ("id3", id3.inq.x, id3.inq.y),
   trace $ ien.clockwise_of ie1,
   trace $ ie2.clockwise_of ien,
   trace $ ie1.implies ien,
   trace $ ie2.implies ien,-/
   ii ← return $ ineq_info.mk_two_comps id1 id2,
--   trace ii,
   if ii.implies id3 = output then skip else fail "didn't match"

section
open tactic interactive interactive.types lean.parser
meta def tactic.interactive.test_ineqs_imply (e1 e2 n : parse qexpr) (output : bool) : tactic unit :=
do e1' ← i_to_expr e1, e2' ← i_to_expr e2, n' ← i_to_expr n, test_ineqs_imply e1' e2' n' output
end

variables x y : ℚ
include x y

example : true :=
begin
test_ineqs_imply (x < 1*y) (x ≥ 2*y) (x > 1*y) ff,
trivial
end

example : true :=
begin
test_ineqs_imply (x < 1*y) (x ≥ 2*y) (x ≤ -1*y) tt,
test_ineqs_imply (x ≥ 1*y) (x ≤ 2*y) (x ≥ -1*y) tt,
test_ineqs_imply (x ≥ 1*y) (x ≤ 2*y) (x > 1*y) ff,
test_ineqs_imply (x < 1*y) (x ≥ 2*y) (x ≤ 1*y) tt,
test_ineqs_imply (x < 1*y) (x ≥ 2*y) (x ≤ 0*y) tt,
test_ineqs_imply (x < 1*y) (x ≥ 2*y) (x > 0*y) ff,
test_ineqs_imply (x < 1*y) (x ≥ 2*y) (x > 1*y) ff,
triv
end

example : true := by do
x ← get_local `x, y ← get_local `y,
e1 ← to_expr `(x < 1*y),
e2 ← to_expr `(x ≥ 2*y),
e3 ← to_expr `(x > 1*y),
(_, _, ie1) ← expr_to_ineq e1,
(_, _, ie2) ← expr_to_ineq e2,
(_, _, ie3) ← expr_to_ineq e3,
id1 ← return $ ineq_data.mk ie1 (ineq_proof.hyp x y _ e1),
id2 ← return $ ineq_data.mk ie2 (ineq_proof.hyp x y _ e1),
id3 ← return $ ineq_data.mk ie3 (ineq_proof.hyp x y _ e1),
bb ← return blackboard.mk_empty,
(_, bb) ← return $ add_ineq id1 bb,
(_, bb) ← return $ add_ineq id2 bb,
trace $ bb.num_comps x y, trace $ bb.contr_found,
(ii, _) ← return $ get_ineqs x y bb,
trace ("implies", ii.implies_ineq id3.inq),
(_, bb) ← return $ add_ineq id3 bb,
trace $ bb.contr_found,
triv

#exit

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
