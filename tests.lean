
import .blackboard .proof_reconstruction .sum_form .prod_form
open polya tactic

meta def expr_to_ineq : expr → tactic (expr × expr × ineq)
| `(%%x ≤ (%%c : ℚ)*%%y) := do c' ← eval_expr rat c, return $ (x, y, ineq.of_comp_and_slope comp.le (slope.some c'))
| `(%%x < (%%c : ℚ)*%%y) := do c' ← eval_expr rat c, return $ (x, y, ineq.of_comp_and_slope comp.lt (slope.some c'))
| `(%%x ≥ (%%c : ℚ)*%%y) := do c' ← eval_expr rat c, return $ (x, y, ineq.of_comp_and_slope comp.ge (slope.some c'))
| `(%%x > (%%c : ℚ)*%%y) := do c' ← eval_expr rat c, return $ (x, y, ineq.of_comp_and_slope comp.gt (slope.some c'))
| _ := failed

meta def expr_to_eq : expr → tactic (expr × expr × ℚ)
| `(%%x = (%%c : ℚ)*%%y) := do c' ← eval_expr rat c, return $ (x, y, c')
| _ := failed


meta def expr_to_sign : expr → tactic (expr × gen_comp)
| `(@eq ℚ %%x (has_zero.zero ℚ)) := return (x, gen_comp.eq)
| `(%%x > (has_zero.zero ℚ)) := return (x, gen_comp.gt)
| `(%%x < (has_zero.zero ℚ)) := return (x, gen_comp.lt)
| `(%%x ≥ (has_zero.zero ℚ)) := return (x, gen_comp.ge)
| `(%%x ≤ (has_zero.zero ℚ)) := return (x, gen_comp.le)
| `(%%x ≠ (has_zero.zero ℚ)) := return (x, gen_comp.ne)
| _ := failed


meta def add_comp_to_blackboard (e : expr) (b : blackboard) : tactic blackboard :=
(do (x, y, ie1) ← expr_to_ineq e,
    id ← return $ ineq_data.mk ie1 (ineq_proof.hyp x y _ e),
--    trace "tac_add_ineq",
    tac_add_ineq b id)
--    return (add_ineq id b).2)
<|>
(do (x, y, ie1) ← expr_to_eq e,
    id ← return $ eq_data.mk ie1 (eq_proof.hyp x y _ e),
--    trace "tac_add_eq",
    tac_add_eq b id)
    --return (add_eq id b).2)
<|>
(do (x, c) ← expr_to_sign e,
    sd ← return $ sign_data.mk c (sign_proof.hyp x _ e),
--    trace "calling tac-add-sign",
    bb ← tac_add_sign b sd,
    trace "tac_add_sign done", return bb)
<|>
fail "add_comp_to_blackboard failed"

meta def add_proof_to_blackboard (b : blackboard) (e : expr) : tactic blackboard :=
(do (x, y, ie1) ← infer_type e >>= expr_to_ineq,
--    trace x, trace y, trace ie1,
    id ← return $ ineq_data.mk ie1 (ineq_proof.hyp x y _ e),
    --return (add_ineq id b).2)
    tac_add_ineq b id)
<|>
(do (x, y, ie1) ← infer_type e >>= expr_to_eq,
    id ← return $ eq_data.mk ie1 (eq_proof.hyp x y _ e),
    --return (add_eq id b).2)
    tac_add_eq b id)
<|>
(do (x, c) ← infer_type e >>= expr_to_sign,
    sd ← return $ sign_data.mk c (sign_proof.hyp x _ e),
--    trace "calling tac-add-sign",
    bb ← tac_add_sign b sd,
--    trace "tac_add_sign done",
    return bb)
<|>
fail "add_comp_to_blackboard failed"

meta def add_proofs_to_blackboard (b : blackboard) (l : list expr) : tactic blackboard :=
monad.foldl add_proof_to_blackboard b l

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

meta def cycle_ops : ℕ → list (polya_state unit) → polya_state ℕ | n ops := 
do set_changed ff,
   ops.mmap' id,
   ch ← is_changed, cntr ← contr_found,
   if ch && bnot cntr then cycle_ops (n+1) ops else return (n+1)

meta def polya_on_hyps (hys : list name) : tactic unit :=
do exps ← hys.mmap get_local,
   bb ← add_proofs_to_blackboard blackboard.mk_empty exps,
   bb.trace_expr_pairs,
/-   trace "-----",
   bb.trace,
   trace "-----",
   (_, bb) ← return $ add_new_ineqs bb,
   trace "-----",
   (_, bb) ← return $ prod_form.add_new_ineqs bb,
   trace "-----",
   (_, bb) ← return $ add_new_ineqs bb,
   trace "-----",
   (_, bb) ← return $ prod_form.add_new_ineqs bb,
   --trace "-----",
   --(_, bb) ← return $ add_new_ineqs bb,
   --(add_new_ineqs >> prod_form.add_new_ineqs) bb,
   trace "-----",
   bb.trace,-/
   (n, bb) ← return $ cycle_ops 0 [add_new_ineqs, prod_form.add_new_ineqs] bb,
   trace ("number of cycles:", n),
   trace ("contr found", bb.contr_found),
   pf ← bb.contr.reconstruct,
   apply pf

section
open tactic interactive interactive.types lean.parser
meta def tactic.interactive.test_ineqs_imply (e1 e2 n : parse lean.parser.pexpr) (output : bool) : tactic unit :=
do e1' ← i_to_expr e1, e2' ← i_to_expr e2, n' ← i_to_expr n, test_ineqs_imply e1' e2' n' output

meta def add_comp_to_blackboard' (e : parse texpr) (b : blackboard) : tactic blackboard :=
do e' ← i_to_expr e, add_comp_to_blackboard e' b

meta def tactic.interactive.polya (ns : parse (many ident)) : tactic unit :=
polya_on_hyps ns

end

--apply `zero_lt_one 
#exit

variables x z y : ℚ
include x y z

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

-- add_new_ineqs not quite right
set_option trace.app_builder true
--set_option pp.all true

set_option profiler true


example (e1 : x < 1*y) (e2 : z < 1*y) (e3 : x + z > 3*y) (e4 : x + z >0) : false := by do 
exps ← monad.mapm get_local [`e1, `e2, `e3, `e4],
bb ← add_proofs_to_blackboard blackboard.mk_empty exps,
bb.trace_exprs, 
(_, bb) ← return $ add_new_ineqs bb, 
bb.trace, 
trace $ ("contr found", bb.contr_found),
pf ← bb.contr.reconstruct,
trace pf, apply pf

--triv


example (e1 : x < 2*y) (e2 : z ≤ 4*y) (e3 : 1*x + 1*z > 6*y) : false := by do 
exps ← monad.mapm get_local [`e1, `e2, `e3],
bb ← add_proofs_to_blackboard blackboard.mk_empty exps,
bb.trace_exprs,
(_, bb) ← return $ add_new_ineqs bb,
bb.trace,
trace $ ("contr found", bb.contr_found),
pf ← bb.contr.reconstruct,
apply pf

--set_option pp.all true
def g (e1 : x = 2*y) (e2 : x > 1*y) (e3 : y < 0)  : false := by do
e1 ← get_local `e1, e2 ← get_local `e2, e3 ← get_local `e3,-- e4 ← get_local `e4,
bb ← add_proofs_to_blackboard blackboard.mk_empty [e1, e2],
bb.trace,
bb ← add_proofs_to_blackboard bb [e3],
bb.trace,
trace $ ("contr found", bb.contr_found),
pf ← bb.contr.reconstruct,
trace pf,
apply pf
#print g
--set_option profiler true


example (e1 : 4*x+7*z = 0) (e2 : (-12)*x + (-3)*y ≤ 0) (e3 : 17*x + (-17)*y + 14*z = 0) (e4 : 9*y + (-17)*z < 0) :
 false := by do  
exps ← monad.mapm get_local [`e1, `e2, `e3, `e4],
bb ← add_proofs_to_blackboard blackboard.mk_empty exps,
bb.trace_exprs,
--(l, _) ← return $ get_add_defs bb,
--trace l,
(_, bb) ← return $ add_new_ineqs bb,
--bb.trace,
trace $ ("contr found", bb.contr_found),
pf ← bb.contr.reconstruct,
apply pf

#exit

example : true := by do
x ← get_local `x, y ← get_local `y, z ← get_local `z,
e1 ← to_expr ```(x < 1*y),
e2 ← to_expr ```(y ≤ 2*z),
e3 ← to_expr ```(x > 2*z),
(_, _, ie1) ← expr_to_ineq e1,
(_, _, ie2) ← expr_to_ineq e2,
(_, _, ie3) ← expr_to_ineq e3,
id1 ← return $ ineq_data.mk ie1 (ineq_proof.hyp x y _ e1),
id2 ← return $ ineq_data.mk ie2 (ineq_proof.hyp y z _ e1),
id3 ← return $ ineq_data.mk ie3 (ineq_proof.hyp x z _ e1),
let sfcd1 : sum_form_comp_data := ⟨sum_form_comp.of_ineq_data id1, sum_form_proof.fake _, mk_rb_map⟩ in
let sfcd2 : sum_form_comp_data := ⟨sum_form_comp.of_ineq_data id2, sum_form_proof.fake _, mk_rb_map⟩ in
let sfcd3 : sum_form_comp_data := ⟨sum_form_comp.of_ineq_data id3, sum_form_proof.fake _, mk_rb_map⟩ in do
trace $ elim_list [sfcd1, sfcd2],
triv

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
trace $ bb.contr_found,
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
