import interactive
variables x y z : α

example
  (e1 : x < 1 * y)
  (e2 : z < 1 * y)
  (e3 : x + z > 3 * y)
  (e4 : x + z > 0)
  : false :=
by polya e1 e2 e3 e4
/-exps ← monad.mapm get_local [`e1, `e2, `e3, `e4],
bb ← add_proofs_to_blackboard blackboard.mk_empty exps,
bb.trace_exprs, 
(_, bb) ← return $ add_new_ineqs bb, 
bb.trace, 
trace $ ("contr found", bb.contr_found),
pf ← bb.contr.reconstruct,
trace pf, apply pf-/

example
  (e1 : x < 2 * y)
  (e2 : z ≤ 4 * y)
  (e3 : 1 * x + 1 * z > 6 * y)
  : false :=
by polya e1 e2 e3
/-do 
exps ← monad.mapm get_local [`e1, `e2, `e3],
bb ← add_proofs_to_blackboard blackboard.mk_empty exps,
bb.trace_exprs,
(_, bb) ← return $ add_new_ineqs bb,
bb.trace,
trace $ ("contr found", bb.contr_found),
pf ← bb.contr.reconstruct,
apply pf-/

def g
  (e1 : x = 2 * y)
  (e2 : x > 1 * y)
  (e3 : y < 0)
  : false :=
by polya e1 e2 e3
/-by do
e1 ← get_local `e1, e2 ← get_local `e2, e3 ← get_local `e3,-- e4 ← get_local `e4,
bb ← add_proofs_to_blackboard blackboard.mk_empty [e1, e2],
bb.trace,
bb ← add_proofs_to_blackboard bb [e3],
bb.trace,
trace $ ("contr found", bb.contr_found),
pf ← bb.contr.reconstruct,
trace pf,
apply pf-/

#exit
example (e1 : 4*x+7*z = 0) (e2 : (-12)*x + (-3)*y ≤ 0) (e3 : 17*x + (-17)*y + 14*z = 0) (e4 : 9*y + (-17)*z < 0) : false :=
by polya e1 e2 e3 e4
