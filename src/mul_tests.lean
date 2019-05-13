import .control
open polya tactic
variables x y z u v w  r : ℚ
--set_option profiler true
--set_option trace.app_builder true

set_option profiler true



example (h1 : u > 0) (h2 : u < 1*v) (h3 : z > 0) (h4 : 1*z + 1*1 < 1*w) (h5 : rat.pow (1*u + 1*v + 1*z) 3 ≥ 1* rat.pow (1*u + 1*v + 1*w + 1*1) 5) : false :=
by  polya h1 h2 h3 h4 h5


example (h1 : u > 1*1) (h2 : u < 1*v) (h3 : rat.pow u 15 > 1*rat.pow v 17) : false :=
by polya h1 h2 h3 

-- reconstruction fails
/-example (h1 : u > 1*1) (h2 : u < 1*v) (h3 : rat.pow u 15 > 1*rat.pow v 19007) : false :=
by polya h1 h2 h3
-/


example (h1 : x > 0) (h2 : x < 1*1) (h3 : rat.pow x 2 ≥ 1*x) : false :=
by  polya h1 h2 h3


/-

0 \leq n, \; n < (K / 2)x, \; 0 < C, \; 0 < \varepsilon < 1 \myRightarrow \left(1 + \frac{\varepsilon}{3 (C + 3)}\right) \cdot n < K x
-/
section
variables n K C eps : ℚ 
example (h1 : 0 ≤ n) (h2 : n < (1/2)*K*x) (h3 : 0 < C) (h4 : 0 < eps) (h5 : eps < 1) (h6 : 1 + (1/3)*eps*rat.pow (C+3) (-1)*n < K*x) : false :=
by polya h1 h2 h3 h4 h5 h6

end


/-
Tests from the old Polya repository.
-/

-- line 44
example  (h1 : u > 0) (h2 : u < 1*v) (h3 : v < 1*1) (h4 : 1 ≤ (1/2)*x) (h5 : x ≤ 1*y) (h6 : ((rat.pow u 2)*x) ≥ (1/2)*(v*rat.pow y 2)) 
: false := 
by polya  h1 h2 h3 h4 h5 h6 --h7 h8

-- line 50
example (h1 : x > 1*1) (h2 : (1 + rat.pow y 2)*x < 1*(1 + rat.pow y 2)) : false :=
by polya h1 h2 


-- line 56
example  (h1 : x > 0) (h2 : x < 1*1) (h3 : rat.pow (1*1 + (-1)*x) (-1) ≤ 1*(rat.pow (1*1 + (-1)*rat.pow x 2) (-1))) : false :=
by
polya h1 h2 h3

-- line 62
example (h1 : u > 0) (h2 : u < 1*v) (h3 : z > 0) (h4 : 1*z + 1*1 < 1*w) (h5 : rat.pow (1*u + 1*v + 1*z) 3 ≥ 1* rat.pow (1*u + 1*v + 1*w + 1*1) 5) : false :=
by  polya h1 h2 h3 h4 h5

-- line 68
example (h1 : u > 0) (h2 : u < 1*v) (h3 : z > 0) (h4 : 1*z + 1*1 < 1*w) (h5 : rat.pow (1*u + 1*v + 1*z) 33 ≥ 1* rat.pow (1*u + 1*v + 1*w + 1*1) 55) : false :=
by  polya h1 h2 h3 h4 h5

-- line 74
-- see top of file. goes forever, normalization problem?
/-example (h1 : u > 0) (h2 : u < 1*(rat.pow (1*rat.pow v 2 + 23*1) 3)) (h3 : z > 0) (h4 : 1*z + 1*1 < 1*w) 
(h5 : rat.pow (1*u + (1*rat.pow (1*rat.pow v 2 + 23*1) 3) + 1*z) 3 ≥ 1*(rat.pow (1*u + 1*rat.pow (1*rat.pow v 2 + 23*1) 3 + 1*w + 1*1) 5)) : false :=
by polya h1 h2 h3 h4 h5-/

-- line 263
-- fails, sign inference too weak
example (h1 : x > 0) (h2 : y < 1*z) (h3 : x * y < 1*(x * z)) : false :=
by polya h1 h2 h3

-- line 295
example (h1 : x * (y+z) ≤ 0) (h2 : y + z > 0) (h3 : x ≥ 0) (h4 : x*w > 0) : false :=
by polya h1 h2 h3 h4

-- line 299
example (h1 : x > 0) (h2 : x < 3*y) (h3 : u < 1*v) (h4 : v < 0) (h5 : 1 < 1*rat.pow v 2) (h6 : rat.pow v 2 < 1*x) (h7 : 1*(u*rat.pow (3*y) 2) + 1*1 ≥ 1*(1*(rat.pow x 2*v) + 1*x)) : false :=
by polya h1 h2 h3 h4 h5 h6

-- line 304 hangs?
/-example (h1 : x > 0) (h2 : x < y) (h3 : 0 < u) (h4 : u < v) (h5 : 0 < w + z) (h6 : w + z < r - 1)
  (h7 : u + (rat.pow (1+x) 2)*(2*w + 2*z + 3) < 2*v + rat.pow (1+y) 2 * (2*r + 1)) : false :=
by polya h1 h2 h3 h4 h5 h6 h7-/

local infix `**`:1000 := rat.pow

#exit
-- line 309
example (h1 : x + rat.pow y (-1) < 2) (h2 : y < 0) (h3 : y * rat.pow x (-1) > 1) (h4 : -2 ≤ x) (h5 : x < 2) (h6 : -2 ≤ y) (h7 : y ≤ 2) (h8 : rat.pow x 2 * rat.pow y (-1) > 1 - x) : false :=
by polya h1 h2 h3 h4 h5 h6 h7 h8
#exit
-- line 314
example (h1 : 0 < u) (h2 : u < v) (h3 : 1 < x) (h4 : x < y) (h5 : 0 < w) (h6 : w < z) (h7 : u + x*w < v+(rat.pow y 2)*z) : false :=
by polya h1 h2 h3 h4 h5 h6 h7

-- line 319
example (h1 : x + rat.pow y (-1) < 2) (h2 : y < 0) (h3 : y * rat.pow x (-1) > 1) (h4 : -2 ≤ x) (h5 : x ≤ 2) (h6 : y ≤ 2) (h7 : -2 ≤ y) (h8 : rat.pow x 2 * rat.pow y (-1) > 1 - x) : false :=
by polya h1 h2 h3 h4 h5 h6 h7 h8

-- 323
example (h1 : 0 < x) (h2 : x < y) (h3 : 0 < u) (h4 : u < v) (h5 : 0 < w + z) (h6 : w + z < r - 1)
          (h7 : u + rat.pow (1 + x) 2 * (2 * w + 2 * z + 3) >= 2 * v + rat.pow (1 + y) 2 * (2 * r + 1)) : false :=
by polya h1 h2 h3 h4 h5 h6 h7

-- 328
example (h1 : 0 < x)  (h2 : x < 3 * y) (h3 : u < v) (h3' : v < 0) (h4 : 1 < v**2) (h5 : v**2 < x) (h6 : u * (3 * y)**2 + 1 >= x**2 * v + x) : false :=
by polya h1 h2 h3 h3' h4 h5 h6

--337
example (h1 : 1 < x) (h2 : 1 < y) (h3 : 1 < z) (h4 : 1 >= x * (1 + z * y)) : false :=
by polya h1 h2 h3 h4

-- 346
example (h1 : x < 1) (h2 : 1 < y) (h3 : x * y > 1) (h4 : u + x >= y + 1) (h5 : x**2 * y < 2 - u * x * y) : false :=
by polya h1 h2 h3 h4 h5

-- 350
example (h1 : x**21 > 0) (h2 : x**3 < 1) (h3 : y**55 > 0) (h4 : y < 1) (h5 : a + b < a * b) : false :=
by polya h1 h2 h3 h4 h5

-- 354
example (h1 : 0 < x) (h2 : y < z) (h3 : y < 0) (h4 : z > 0) (h5 : x * y ≥ x * z) : false :=
by polya h1 h2 h3 h4 h5

--359
example (h1 : 0 < z) (h2 : y < z) (h3 : y = 0) (h4 : z > 0) (h5 : x * y ≥ x * z) : false :=
by polya h1 h2 h3 h4 h5

-- 371
example (h1 : x > 1) (h2 : z = y**2) (h3 : 1+z*x < 1+z) : false :=
by polya h1 h2 h3

-- 384
example (h1 : x = z) (h2 : y = w) (h3 : x > 0) (h4 : y > 0) (h5 : x * y ≠ z * w) : false :=
by polya h1 h2 h3 h4 h5

-- 389
example (h1 : x > 2*y) (h2 : x = 3*y) (h3 : y ≤ 0) : false :=
by polya h1 h2 h3

example (h1 : x > 0) (h2 : 1 < 1 * x) (h3 : 1 < 1 * (rat.pow x (-1))) : false :=
by polya h1 h2 h3


example  (h1 : x > 0) (h2 : x < 1*1) (h3 : rat.pow (1*1 + (-1)*x) (-1) ≤ 1*(rat.pow (1*1 + (-1)*rat.pow x 2) (-1))) : false :=
by 
polya h1 h2 h3




example (h1 : x > 1*1) (h1' : y ≥ 0) (h2 : (1 + y)*x < 1*(1 + y)) : false :=
by polya  h1 h1' h2 



example (e1 : x > 0) /-(e2' : x*y > 0)-/ (e2' : y > 0) (e2 : x > 1*y) (e3 : z > 1*x) (e3' : z > 0) (e4 : y > 1*z) : false :=
by polya e1 e2' e2 e3 e3' e4

example (e1 : x > 0) (e2 : y > 0) (e2' : z > 0) (e3 : y > 1*z) (e4 : x > 1*z) (e5 : x*y<1*(rat.pow z 2))  : false :=
by polya e1 e2 e2' e3 e4 e5 


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
 
