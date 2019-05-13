import .datatypes .blackboard 

-- TODO: maybe more of this can move to datatypes

namespace polya


section sfcd_to_ineq

 -- assumes lhs < rhs as exprs. cl*lhs + cr*rhs R 0 ==> ineq_data
private meta def mk_ineq_data_of_lhs_rhs (lhs rhs : expr) (cl cr : ℚ) (c : comp) {s} (pf : sum_form_proof s) :
        Σ l r, ineq_data l r :=
let c' := if cl > 0 then c else c.reverse,
    iq := ineq.of_comp_and_slope (c') (slope.some (-cr/cl)) in
⟨lhs, rhs, ⟨iq, ineq_proof.of_sum_form_proof lhs rhs iq pf⟩⟩

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
  | [(rhs, cr), (lhs, cl)] := some ⟨lhs, rhs, ⟨(-cr/cl), eq_proof.of_sum_form_proof _ _ _ prf⟩⟩
  | _ := none
  end
| _ := none 



meta def sum_form_comp_data.to_sign_data : sum_form_comp_data → option Σ e, sign_data e
| ⟨sfc, prf, _⟩ := 
  match sfc.sf.get_nonzero_factors with
  | [(e, n)] := 
   let c := if n < 0 then sfc.c.to_gen_comp.reverse else sfc.c.to_gen_comp in
   some ⟨e, ⟨c, sign_proof.of_sum_form_proof _ _ prf⟩⟩ --sign_proof.adhoc _ _ (prf.reconstruct >>= tactic.trace, tactic.fail "sum_form_comp_data.to_sign_data not implemented")⟩⟩
  | _ := none
  end

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
  some ⟨_, sum_form_proof.of_add_eq_factor_op_comp fac prf2 (by rw ←hce; apply prf1), (rb_set.union elim_list1 elim_list2).insert pvt⟩ 
else if hce' : c2 = spec_comp.eq then
  some ⟨_, sum_form_proof.of_add_eq_factor_op_comp fac prf1 (by rw ←hce'; apply prf2), (rb_set.union elim_list1 elim_list2).insert pvt⟩
else none

meta def sum_form_comp_data.elim_expr (sfcd1 sfcd2 : sum_form_comp_data) (pvt : expr) : option sum_form_comp_data :=
if sfcd1.get_coeff pvt = 0 then some ⟨sfcd1.sfc, sfcd1.prf, sfcd1.elim_list.insert pvt⟩
else if sfcd2.get_coeff pvt = 0 then none
else sum_form_comp_data.elim_expr_aux sfcd1 sfcd2 pvt

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

private meta def check_elim_lists_aux (sfcd1 sfcd2 : sum_form_comp_data) : bool :=
sfcd1.vars.all (λ e, bnot (sfcd2.elim_list.contains e))

private meta def check_elim_lists (sfcd1 sfcd2 : sum_form_comp_data) : bool :=
check_elim_lists_aux sfcd1 sfcd2 && check_elim_lists_aux sfcd2 sfcd1

meta def sum_form_comp_data.needs_elim_against (sfcd1 sfcd2 : sum_form_comp_data) (e : expr) : bool :=
(check_elim_lists sfcd1 sfcd2)-- &&
 --(((sfcd1.vars.append sfcd2.vars).filter (λ e' : expr, e'.lt e)).length ≤ 2) -- change back to e' lt e

/--
 Uses sfcd to eliminate the e from all comparisons in cmps, and adds the new comparisons to rv
-/
meta def elim_expr_from_comp_data_filtered (sfcd : sum_form_comp_data) (cmps : rb_set sum_form_comp_data) 
         (e : expr) (rv : rb_set sum_form_comp_data) : rb_set sum_form_comp_data :=
cmps.fold rv (λ c rv', if sfcd.needs_elim_against c e then sfcd.elim_into c e rv' else rv')


/--
 Performs all possible eliminations with sfcd on cmps. Returns a set of all new comps, NOT including the old ones.
-/
meta def new_exprs_from_comp_data_set (sfcd : sum_form_comp_data) (cmps : rb_set sum_form_comp_data) : rb_set sum_form_comp_data :=
sfcd.vars.foldr (λ e rv, elim_expr_from_comp_data_filtered sfcd cmps e rv) mk_rb_set


meta def elim_list_into_set : rb_set sum_form_comp_data → list sum_form_comp_data → rb_set sum_form_comp_data
| cmps [] := cmps
| cmps (sfcd::new_cmps) :=
   let sfcdn := sfcd.normalize in
   if cmps.contains (/-trace_val-/ (new_cmps.length, sfcdn)).2 then elim_list_into_set cmps new_cmps else
   let new_gen := (new_exprs_from_comp_data_set sfcdn cmps).keys in
   elim_list_into_set (cmps.insert sfcdn) (new_cmps.append new_gen)


meta def elim_list_set (cmps : list sum_form_comp_data) (start : rb_set sum_form_comp_data := mk_rb_set) : rb_set sum_form_comp_data :=
elim_list_into_set start (trace_val cmps)

meta def elim_list (cmps : list sum_form_comp_data) (start : rb_set sum_form_comp_data := mk_rb_set) : list sum_form_comp_data :=
(elim_list_into_set start cmps).to_list

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
  do il ← get_ineq_list,  el ← get_eq_list, sl ← get_sign_list, dfs ← get_add_defs,
   let il' := il.map (λ ⟨lhs, rhs, id⟩, sum_form_comp_data.of_ineq_data id) in
   let el' := el.map (λ ⟨_, _, ed⟩, sum_form_comp_data.of_eq_data ed) in
   let sl' := sl.map (λ ⟨_, sd⟩, sum_form_comp_data.of_sign_data sd) in
   let dfs' := dfs.map mk_eqs_of_expr_sum_form_pair in
   return $ (((il'.append el').append sl').append dfs').qsort (λ a b, if has_ordering.cmp a b = ordering.lt then tt else ff)

private meta def mk_eq_list (cmps : list sum_form_comp_data) : list Σ lhs rhs, eq_data lhs rhs :=
let il := cmps.map (λ sfcd, sfcd.to_eq_data) in
reduce_option_list il

private meta def mk_ineq_list (cmps : list sum_form_comp_data) : list Σ lhs rhs, ineq_data lhs rhs :=
let il := cmps.map (λ sfcd, sfcd.to_ineq_data) in
reduce_option_list il

private meta def mk_sign_list (cmps : list sum_form_comp_data) : list Σ e, sign_data e :=
let il := cmps.map (λ sfcd, sfcd.to_sign_data) in
reduce_option_list il

meta def sum_form.add_new_ineqs (start : rb_set sum_form_comp_data := mk_rb_set) : polya_state (rb_set sum_form_comp_data) :=
do is_contr ← contr_found,
   if (/-trace_val-/ ("is_contr", is_contr)).2 then return start else do
   sfcds ← mk_sfcd_list, 
   let elim_set := elim_list_set sfcds start,
   let elims := elim_set.to_list, 
   let ineqs := mk_ineq_list elims,
   let eqs   := mk_eq_list elims,
   let signs := (/-trace_val-/ ("found signs:", mk_sign_list elims)).2,
   ineqs.mmap' (λ s, add_ineq s.2.2),
   eqs.mmap' (λ s, add_eq s.2.2),
   signs.mmap' (λ s, add_sign s.2),
   return elim_set


end bb_process

end polya
