import .datatypes .struct_eta .blackboard  --.proof_reconstruction

-- TODO: maybe more of this can move to datatypes

namespace polya


section sfcd_to_ineq

/-theorem fake_ineq_to_expr_proof (P : Prop) {Q : Prop} (h : Q) : P := sorry

meta def ineq.to_expr (lhs rhs : expr) (id : ineq) {s} (pf : sum_form_proof s) : tactic expr :=
do tp ← id.to_type lhs rhs,
   prf ← pf.reconstruct,
   tactic.mk_app ``fake_ineq_to_expr_proof [tp, prf]-/

 -- assumes lhs < rhs as exprs. cl*lhs + cr*rhs R 0 ==> ineq_data
private meta def mk_ineq_data_of_lhs_rhs (lhs rhs : expr) (cl cr : ℚ) (c : comp) {s} (pf : sum_form_proof s) :
        Σ l r, ineq_data l r :=
let c' := if cl > 0 then c else c.reverse,
    iq := ineq.of_comp_and_slope (c') (slope.some (-cr/cl)) in
⟨lhs, rhs, ⟨iq, ineq_proof.of_sum_form_proof lhs rhs iq pf⟩⟩ --_ _ _ (iq.to_expr lhs rhs pf)⟩⟩ -- TODO
--⟨lhs, rhs, ⟨iq, ineq_proof.hyp _ _ _ ```(0)⟩⟩ -- TODO

/--- assumes lhs < rhs as exprs. cl*lhs + cr*rhs R 0 ==> ineq_data
private meta def mk_ineq_of_lhs_rhs (cl cr : ℚ) (c : comp) : ineq :=
let c' := if cl > 0 then c else c.reverse in
ineq.of_comp_and_slope (c') (slope.some (-cr/cl))-/

-- we need a proof constructor for ineq and eq
meta def sum_form_comp_data.to_ineq_data : sum_form_comp_data → option (Σ lhs rhs, ineq_data lhs rhs) 
| ⟨⟨sf, spec_comp.eq⟩, prf, _⟩ := none
| ⟨sfc, prf, _⟩ := 
  match sfc.sf.get_nonzero_factors with
  | [(rhs, cr), (lhs, cl)] := 
    if rhs.lt lhs then mk_ineq_data_of_lhs_rhs lhs rhs cl cr (sfc.c.to_comp) prf
    else  mk_ineq_data_of_lhs_rhs rhs lhs cr cl (sfc.c.to_comp) prf
  | _ := none
  end

meta def sum_form_comp_data.to_eq_data : sum_form_comp_data → option (Σ lhs rhs, eq_data lhs rhs)
| ⟨⟨sf, spec_comp.eq⟩, prf, _⟩ :=
  match sf.get_nonzero_factors with
  | [(rhs, cr), (lhs, cl)] := some ⟨lhs, rhs, ⟨(-cr/cl), eq_proof.hyp _ _ _ `(0 : ℚ)⟩⟩ -- TODO
  | _ := none
  end
| _ := none 

end sfcd_to_ineq


-- assumes the coeff of pvt in both is nonzero. Does not enforce elim_list preservation
meta def sum_form_comp_data.elim_expr_aux : sum_form_comp_data → sum_form_comp_data → expr → 
     option sum_form_comp_data
| ⟨⟨sf1, c1⟩, prf1, elim_list1⟩ ⟨⟨sf2, c2⟩, prf2, elim_list2⟩ pvt := 
let cf1 := sf1.get_coeff pvt,
    cf2 := sf2.get_coeff pvt,
    fac := (-cf1/cf2) in
if (fac > 0) then
  some ⟨_, sum_form_proof.of_add_factor_same_comp fac prf1 prf2, (rb_set.union elim_list1 elim_list2).insert pvt⟩
else if hce : c1 = spec_comp.eq then
  some ⟨_, sum_form_proof.of_add_eq_factor_op_comp fac prf2 (by rw -hce; apply prf1), (rb_set.union elim_list1 elim_list2).insert pvt⟩ 
else if hce' : c2 = spec_comp.eq then
  some ⟨_, sum_form_proof.of_add_eq_factor_op_comp fac prf1 (by rw -hce'; apply prf2), (rb_set.union elim_list1 elim_list2).insert pvt⟩
else none

meta def sum_form_comp_data.elim_expr (sfcd1 sfcd2 : sum_form_comp_data) (pvt : expr) : option sum_form_comp_data :=
if sfcd1.get_coeff pvt = 0 then some sfcd1
else if sfcd2.get_coeff pvt = 0 then none
else sum_form_comp_data.elim_expr_aux sfcd1 sfcd2 pvt

/-private meta def compare_coeffs (sf1 sf2 : sum_form) (h : expr) : ordering :=
let c1 := sf1.get_coeff h, c2 := sf2.get_coeff h in
if c1 < c2 then ordering.lt else if c2 < c1 then ordering.gt else ordering.eq

private meta def compare_coeff_lists (sf1 sf2 : sum_form) : list expr → list expr → ordering
| [] [] := ordering.eq
| [] _ := ordering.lt
| _ [] := ordering.gt
| (h1::t1) (h2::t2) := 
   if h1 = h2 then let ccomp := compare_coeffs sf1 sf2 h1 in
     if ccomp = ordering.eq then compare_coeff_lists t1 t2 else ccomp
   else has_ordering.cmp h1 h2

meta def sum_form.order (sf1 sf2 : sum_form) : ordering :=
compare_coeff_lists sf1 sf2 sf1.keys sf2.keys

meta def sum_form_comp.order : sum_form_comp → sum_form_comp → ordering
| ⟨_, spec_comp.lt⟩ ⟨_, spec_comp.le⟩ := ordering.lt
| ⟨_, spec_comp.lt⟩ ⟨_, spec_comp.eq⟩ := ordering.lt
| ⟨_, spec_comp.le⟩ ⟨_, spec_comp.eq⟩ := ordering.lt
| ⟨sf1, _⟩ ⟨sf2, _⟩ := sum_form.order sf1.normalize sf2.normalize

-- TODO: do we need to take elim_vars into account for this order?
meta def sum_form_comp_data.order : sum_form_comp_data → sum_form_comp_data → ordering
| ⟨sfc1, _, _⟩ ⟨sfc2, _, _⟩ := sfc1.order sfc2-/

-- this is a crazy hack.
/-meta def sum_form_comp_data.order :=
λ c1 c2 : sum_form_comp_data, has_ordering.cmp ((to_fmt c1).to_string options.mk).to_name ((to_fmt c2).to_string options.mk).to_name
-/
 


/-meta def sum_form_comp_data.elim_into (sfcd1 sfcd2 : sum_form_comp_data) (pvt : expr)
     (rv : list sum_form_comp_data) : list sum_form_comp_data :=
match sfcd1.elim_expr sfcd2 pvt with
| none := rv
| some sfcd := sfcd::rv
end

meta def elim_expr_from_comp_data (sfcd : sum_form_comp_data) (cmps : list sum_form_comp_data) 
         (e : expr) (rv : list sum_form_comp_data) : list sum_form_comp_data :=
cmps.foldr (λ c rv', sfcd.elim_into c e rv') rv

meta def elim_expr_from_comp_data_set (cmps : list sum_form_comp_data) (e : expr) : list sum_form_comp_data :=
cmps.foldr (λ c rv, elim_expr_from_comp_data c cmps e rv) []-/

meta def sum_form_comp_data.elim_into (sfcd1 sfcd2 : sum_form_comp_data) (pvt : expr)
     (rv : rb_set sum_form_comp_data) : rb_set sum_form_comp_data :=
match sfcd1.elim_expr sfcd2 pvt with
| none := rv
| some sfcd := rv.insert sfcd
end

/--
 Uses sfcd to eliminate the e from all comparisons in cmps, and adds the new comparisons to rv
-/
meta def elim_expr_from_comp_data (sfcd : sum_form_comp_data) (cmps : rb_set sum_form_comp_data) 
         (e : expr) (rv : rb_set sum_form_comp_data) : rb_set sum_form_comp_data :=
cmps.fold rv (λ c rv', sfcd.elim_into c e rv')

/--
 Eliminates the expression e from all comparisons in cmps in all possible ways
-/
meta def elim_expr_from_comp_data_set (cmps : rb_set sum_form_comp_data) (e : expr) : rb_set sum_form_comp_data :=
cmps.fold mk_rb_set (λ c rv, elim_expr_from_comp_data c cmps e rv)

/-
/--
 Performs all possible eliminations with sfcd on cmps. Returns a set of all new comps, NOT including the old ones.
-/
meta def new_exprs_from_comp_data_set (sfcd : sum_form_comp_data) (cmps : rb_set sum_form_comp_data) : rb_set sum_form_comp_data :=
sfcd.vars.foldr (λ e rv, elim_expr_from_comp_data sfcd cmps e rv) mk_rb_set
-/

meta def elim_expr_from_comp_data_list (cmps : list sum_form_comp_data) (e : expr) : list sum_form_comp_data :=
(elim_expr_from_comp_data_set (rb_set.of_list cmps) e).to_list

/-
/--
 Adds sfcd to comps. Then generates all new comparisons between sfcd and comps, and recursively adds those.
-/
meta def elim_and_add : sum_form_comp_data → rb_set sum_form_comp_data → rb_set sum_form_comp_data | sfcd cmps :=
let new_comps := new_exprs_from_comp_data_set sfcd cmps in
(trace_val new_comps).fold (cmps.insert sfcd) elim_and_add

meta def elim_set (cmps : rb_set sum_form_comp_data) : rb_set sum_form_comp_data :=
cmps.fold mk_rb_set elim_and_add

meta def elim_list (cmps : list sum_form_comp_data) : list sum_form_comp_data :=
(elim_set (rb_set.of_list cmps)).to_list
-/

private meta def check_elim_lists_aux (sfcd1 sfcd2 : sum_form_comp_data) : bool :=
sfcd1.vars.all (λ e, bnot (sfcd2.elim_list.contains e))

private meta def check_elim_lists (sfcd1 sfcd2 : sum_form_comp_data) : bool :=
check_elim_lists_aux sfcd1 sfcd2 && check_elim_lists_aux sfcd2 sfcd1

meta def sum_form_comp_data.needs_elim_against (sfcd1 sfcd2 : sum_form_comp_data) (e : expr) : bool :=
(check_elim_lists sfcd1 sfcd2) &&
 (((sfcd1.vars.append sfcd2.vars).filter (λ e' : expr, e'.lt e)).length ≤ 2)

/--
 Uses sfcd to eliminate the e from all comparisons in cmps, and adds the new comparisons to rv
-/
meta def elim_expr_from_comp_data_filtered (sfcd : sum_form_comp_data) (cmps : rb_set sum_form_comp_data) 
         (e : expr) (rv : rb_set sum_form_comp_data) : rb_set sum_form_comp_data :=
cmps.fold rv (λ c rv', if sfcd.needs_elim_against c e then sfcd.elim_into c e rv' else rv')

/-
/--
 Eliminates the expression e from all comparisons in cmps in all possible ways
-/
meta def elim_expr_from_comp_data_set (cmps : rb_set sum_form_comp_data) (e : expr) : rb_set sum_form_comp_data :=
cmps.fold mk_rb_set (λ c rv, elim_expr_from_comp_data c cmps (trace_val e) rv)
-/


/--
 Performs all possible eliminations with sfcd on cmps. Returns a set of all new comps, NOT including the old ones.
-/
meta def new_exprs_from_comp_data_set (sfcd : sum_form_comp_data) (cmps : rb_set sum_form_comp_data) : rb_set sum_form_comp_data :=
sfcd.vars.foldr (λ e rv, elim_expr_from_comp_data_filtered sfcd cmps e rv) mk_rb_set


meta def elim_list_into_set : rb_set sum_form_comp_data → list sum_form_comp_data → rb_set sum_form_comp_data
| cmps [] := cmps
| cmps (sfcd::new_cmps) :=
   if (trace_val (cmps.contains (trace_val sfcd)) : bool) then elim_list_into_set cmps new_cmps else
   let new_gen := (new_exprs_from_comp_data_set sfcd.normalize cmps).keys in
   elim_list_into_set (cmps.insert sfcd) (new_cmps.append new_gen)


/-

meta def elim_list_into_set : rb_set sum_form_comp_data → list sum_form_comp_data → rb_set sum_form_comp_data
| cmps [] := cmps
| cmps (sfcd::new_cmps) :=
   if (trace_val (cmps.contains (trace_val sfcd)) : bool) then elim_list_into_set cmps new_cmps else
   let new_gen := (new_exprs_from_comp_data_set sfcd.normalize cmps).keys in
   elim_list_into_set (rb_set.insert_list (cmps.insert sfcd) new_gen) new_cmps -- (new_cmps.append new_gen)-/

meta def elim_list (cmps : list sum_form_comp_data) : list sum_form_comp_data :=
(elim_list_into_set mk_rb_set cmps).to_list

meta def vars_of_sfcd_set (cmps : rb_set sum_form_comp_data) : rb_set expr :=
cmps.fold mk_rb_set (λ sfcd s, s.insert_list sfcd.vars)


def list.first {α} (P : α → bool) : list α → option α 
| [] := none
| (h::t) := if P h then some h else list.first t


meta def find_contrad_sfcd_in_sfcd_set (cmps : rb_set sum_form_comp_data) : option sum_form_comp_data :=
let elimd := (vars_of_sfcd_set cmps).fold cmps (λ s cmps', elim_expr_from_comp_data_set cmps' s) in
list.first sum_form_comp_data.is_contr elimd.keys -- dot notation doesn't work here??

meta def find_contrad_sfcd_in_sfcd_list (cmps : list sum_form_comp_data) : option sum_form_comp_data :=
find_contrad_sfcd_in_sfcd_set (rb_set.of_list cmps)

meta def find_contrad_in_sfcd_set (cmps : rb_set sum_form_comp_data) : option contrad :=
do sfcd ← find_contrad_sfcd_in_sfcd_set cmps,
   return $ contrad.sum_form sfcd.prf

meta def find_contrad_in_sfcd_list (cmps : list sum_form_comp_data) : option contrad :=
find_contrad_in_sfcd_set (rb_set.of_list cmps)

meta def is_inconsistent (cmps : rb_set sum_form_comp_data) : bool :=
(find_contrad_sfcd_in_sfcd_set cmps).is_some

meta def is_inconsistent_list (cmps : list sum_form_comp_data) : bool :=
is_inconsistent $ rb_set.of_list cmps


section bb_process

meta def mk_eqs_of_expr_sum_form_pair : expr × sum_form → sum_form_comp_data
| (e, sf) := 
  let sf' := sf - (sum_form.of_expr e) in
  ⟨⟨sf', spec_comp.eq⟩, sum_form_proof.of_expr_def e sf', mk_rb_set⟩

private meta def mk_sfcd_list : polya_state (list sum_form_comp_data) :=
do il ← get_ineq_list, il ← return (trace_val ("il",il)).2, el ← get_eq_list, sl ← get_sign_list, dfs ← get_add_defs,
   let il' := il.map (λ ⟨lhs, rhs, id⟩, sum_form_comp_data.of_ineq_data id) in
   let el' := el.map (λ ⟨_, _, ed⟩, sum_form_comp_data.of_eq_data ed) in
   let sl' := sl.map (λ ⟨_, sd⟩, sum_form_comp_data.of_sign_data sd) in
   let dfs' := dfs.map mk_eqs_of_expr_sum_form_pair in
   return $ (((il'.append el').append sl').append dfs').qsort (λ a b, if has_ordering.cmp a b = ordering.lt then tt else ff)


private meta def mk_ineq_list (cmps : list sum_form_comp_data) : list Σ lhs rhs, ineq_data lhs rhs :=
let il := cmps.map (λ sfcd, sfcd.to_ineq_data) in
reduce_option_list il
#check @monad.mapm'
meta def add_new_ineqs : polya_state unit :=
do sfcds ← mk_sfcd_list,
   let ineqs := mk_ineq_list $ elim_list sfcds in
   monad.mapm' 
  (λ s : Σ lhs rhs, ineq_data lhs rhs, add_ineq (trace_val ("derived ineq", s.2.2)).2)
--  (λ ⟨lhs, rhs,id⟩ : Σ lhs rhs, ineq_data lhs rhs, add_ineq id)
 ineqs

end bb_process

end polya
#exit
section tests
#print instances reflected
--set_option pp.all true
#check `(ℚ) 

variables x y z : ℚ
/-meta def x' : expr := `(x)
meta def y' : expr := `(y)
meta def z' : expr := `(z)-/


open tactic
#print declaration
#check reducibility_hints
include x y z
def aux : ℕ := by do x ← get_local `x, 
match x with
| expr.local_const nm ppnm bi tp :=
 (add_decl $ declaration.defn `x' [] `(expr) `(expr.local_const nm ppnm bi tp) reducibility_hints.abbrev ff) >> apply ↑`(0)
| _ := apply ↑`(0)
end

open tactic polya rb_map
meta def e1 : sum_form := of_list [(x', 3), (y', 2), (z', 1)] -- 3x + 2y + z
meta def e2 : sum_form := of_list [(x', -2), (y',1/2)]
meta def e3 : sum_form := of_list [(y',-5), (z', 4)]
meta def e4 : sum_form := of_list [(x', 10), (y',-1)]
meta def e5 : sum_form := of_list [(z', 1), (y',1)]
meta def e6 : sum_form := of_list [(z', 1)]

meta def c1 : sum_form_comp := ⟨e1, spec_comp.le⟩ -- 3x + 2y + z ≤ 0
meta def c2 : sum_form_comp := ⟨e2.negate, spec_comp.lt⟩
meta def c3 : sum_form_comp := ⟨e3.negate, spec_comp.le⟩
meta def c4 : sum_form_comp := ⟨e4, spec_comp.eq⟩
meta def c5 : sum_form_comp := ⟨e5.negate, spec_comp.lt⟩
meta def c6 : sum_form_comp := ⟨e6, spec_comp.lt⟩

meta def d1 : sum_form_comp_data := ⟨c1, sum_form_proof.fake _, mk_rb_set⟩
meta def d2 : sum_form_comp_data := ⟨c2, sum_form_proof.fake _, mk_rb_set⟩
meta def d3 : sum_form_comp_data := ⟨c3, sum_form_proof.fake _, mk_rb_set⟩
meta def d4 : sum_form_comp_data := ⟨c4, sum_form_proof.fake _, mk_rb_set⟩
meta def d5 : sum_form_comp_data := ⟨c5, sum_form_proof.fake _, mk_rb_set⟩
meta def d6 : sum_form_comp_data := ⟨c6, sum_form_proof.fake _, mk_rb_set⟩

#eval is_inconsistent_list [d1, d3, d5, d6]

run_cmd trace $ d1.elim_expr d2 y'

run_cmd trace $ 
elim_expr_from_comp_data_list 
 (elim_expr_from_comp_data_list [d1, d3,  d5, d6] x')
  y'

run_cmd trace $ 
elim_expr_from_comp_data_list
 (elim_expr_from_comp_data_list 
  (elim_expr_from_comp_data_list [d1, d3,  d5, d6] x')
   y')
  z'


run_cmd trace $
elim_list [d4, d5, d6]


run_cmd trace $
elim_list  [d1, d3, d5] --[d1, d3,  d5, d6]

end tests
