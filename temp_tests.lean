import .tests
open polya tactic
variables x y z u v : ℚ
set_option profiler true

example (h0 : (1 : ℚ) > 0) (h1 : 0 < 1*u) (h2 : u < 1*v) (h3 : v < 1*1) (h4 : 1 ≤ (1/2)*x) (h5 : x ≤ 1*y) (h6 : ((rat.pow u 2)*x) ≥ (1/2)*(v*rat.pow y 2)) (h7 : rat.pow y 2 ≥ 0) (h8 : rat.pow u 2 ≥ 0) : false := 
by polya h0 h1 h2 h3 h4 h5 h6 h7 h8
 /-do
exps ← monad.mapm get_local [`h0, `h1, `h2, `h3, `h4, `h5, `h6],
bb ← add_proofs_to_blackboard blackboard.mk_empty exps,
bb.trace_exprs,
trace "-----",
bb.trace,
trace "-----",
(_, bb) ← return $ add_new_ineqs bb,
(_, bb) ← return $ prod_form.add_new_ineqs bb,
(_, bb) ← return $ add_new_ineqs bb,
trace "-----", 
bb.trace,
trace $ ("contr found", bb.contr_found),
pf ← bb.contr.reconstruct,
apply pf-/
example (h0 : (1 : ℚ) > 0) (h1 : x > 1*1) (h2 : (1 + rat.pow y 2)*x < 1*(1 + rat.pow y 2)) : false :=
by polya h0 h1 h2 

example (h0 : (1 : ℚ) > 0) (h1 : x > 1*1) (h1' : y ≥ 0) (h2 : (1 + y)*x < 1*(1 + y)) : false :=
by polya h0 h1 h1' h2
#exit

/-set_option trace.app_builder true
example (h0 : (1 : ℚ) > 0) (h1 : x > 1*1) (h1' : y ≥ 0) (h2 : (1 + y)*x < 1*(1 + y)) : false :=
by do
exps ← monad.mapm get_local [`h0,  `h1, `h1', `h2],
bb ← add_proofs_to_blackboard blackboard.mk_empty exps,
bb.trace_exprs,
trace "-----",
bb.trace,
trace "-----",
(_, bb) ← return $ add_new_ineqs bb,
(_, bb) ← return $ prod_form.add_new_ineqs bb,
--(_, bb) ← return $ add_new_ineqs bb,
--(_, bb) ← return $ prod_form.add_new_ineqs bb,
trace "-----", 
bb.trace,
trace $ ("contr found", bb.contr_found),
pf ← bb.contr.reconstruct,
apply pf

#exit
example (h0 : (1 : ℚ) > 0) (h1 : x > 1*1) (h2 : (1 + rat.pow y 2)*x < 1*(1 + rat.pow y 2)) (ht : rat.pow y 2 ≥ 0) : false :=
by do
exps ← monad.mapm get_local [`h0,  `h1, `h2, `ht],
bb ← add_proofs_to_blackboard blackboard.mk_empty exps,
bb.trace_exprs,
trace "-----",
bb.trace,
trace "-----",
(_, bb) ← return $ add_new_ineqs bb,
(_, bb) ← return $ prod_form.add_new_ineqs bb,
(_, bb) ← return $ add_new_ineqs bb,
(_, bb) ← return $ prod_form.add_new_ineqs bb,
trace "-----", 
bb.trace,
trace $ ("contr found", bb.contr_found),
pf ← bb.contr.reconstruct,
apply pf-/

#exit

set_option trace.app_builder true
--set_option pp.implicit true
--set_option pp.numerals false
-- left off with : bug at prod_form.to_expr??
example (e1 : x > 0) /-(e2' : x*y > 0)-/ (e2' : y > 0) (e2 : x > 1*y) (e3 : z > 1*x) (e3' : z > 0) (e4 : y > 1*z) : false :=
by do 
exps ← monad.mapm get_local [`e1, `e2, `e2', `e3, `e3', `e4],
bb ← add_proofs_to_blackboard blackboard.mk_empty exps,
bb.trace_exprs,
trace "-----",
bb.trace,
trace "-----",
(_, bb) ← return $ prod_form.add_new_ineqs bb,
trace "-----", 
bb.trace,
trace $ ("contr found", bb.contr_found),
pf ← bb.contr.reconstruct,
apply pf



#exit

example (e1 : x > 0) (e2 : y > 0) (e2' : z > 0) (e3 : y > 1*z) (e4 : x > 1*z) (e5 : x*y<1*(rat.pow z 2)) (e6 : rat.pow z 2 > 0) (e7 : x*y > 0) : false :=
by do 
exps ← monad.mapm get_local [`e1, `e2, `e2', `e3, `e4, `e5, `e6, `e7],
bb ← add_proofs_to_blackboard blackboard.mk_empty exps,
bb.trace_exprs,
--(l, _) ← return $ get_add_defs bb,
--trace l,
(_, bb) ← return $ prod_form.add_new_ineqs bb,

--bb.trace,
trace $ ("contr found", bb.contr_found),
pf ← bb.contr.reconstruct,
apply pf
 
