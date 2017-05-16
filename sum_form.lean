import .datatypes .struct_eta

namespace polya

inductive spec_comp
| lt | le | eq

def spec_comp_and_flipped_of_comp : comp → spec_comp × bool
| comp.lt := (spec_comp.lt, ff)
| comp.le := (spec_comp.le, ff)
| comp.gt := (spec_comp.lt, tt)
| comp.ge := (spec_comp.le, tt)

def spec_comp.strongest : spec_comp → spec_comp → spec_comp
| spec_comp.lt _ := spec_comp.lt
| _ spec_comp.lt := spec_comp.lt
| spec_comp.le _ := spec_comp.le
| _ spec_comp.le := spec_comp.le
| spec_comp.eq spec_comp.eq := spec_comp.eq

/--
 This is nonsense on eq
-/
def spec_comp.to_comp : spec_comp → comp
| spec_comp.lt := comp.lt
| spec_comp.le := comp.le
| spec_comp.eq := comp.gt

meta def spec_comp.to_format : spec_comp → format
| spec_comp.lt := "<"
| spec_comp.le := "≤"
| spec_comp.eq := "="

meta instance spec_comp.has_to_format : has_to_format spec_comp :=
⟨spec_comp.to_format⟩

@[reducible]
meta def sum_form := rb_map expr ℚ

meta def sum_form.zero : sum_form := rb_map.mk _ _
meta instance : has_zero sum_form := ⟨sum_form.zero⟩

meta def sum_form.of_expr (e : expr) : sum_form := 
mk_rb_map.insert e 1

meta def sum_form.get_coeff (sf : sum_form) (e : expr) : ℚ :=
match sf.find e with
| some q := q
| none := 0
end

meta def sum_form.get_nonzero_factors (sf : sum_form) : list (expr × ℚ) :=
sf.to_list

meta def sum_form.add_coeff (sf : sum_form) (e : expr) (c : ℚ) : sum_form :=
if (sf.get_coeff e) + c = 0 then sf.erase e
else sf.insert e ((sf.get_coeff e) + c)

meta def sum_form.add (lhs rhs : sum_form) : sum_form :=
rhs.fold lhs (λ e q sf, sf.add_coeff e q)

meta def sum_form.scale (sf : sum_form) (c : ℚ) : sum_form :=
sf.map (λ q, if q=1/c then 1 else c*q) -- replace this with a real implementation of ℚ

meta def sum_form.sub (lhs rhs : sum_form) : sum_form :=
lhs.add (rhs.scale (-1))

meta def sum_form.negate (lhs : sum_form) : sum_form :=
lhs.scale (-1)

meta instance : has_add sum_form := ⟨sum_form.add⟩
meta instance : has_sub sum_form := ⟨sum_form.sub⟩

meta def sum_form.add_factor (lhs rhs : sum_form) (c : ℚ) : sum_form :=
lhs + (rhs.scale c)

meta structure sum_form_comp :=
(sf : sum_form) (c : spec_comp) 

/-meta def sum_form_comp.reverse (sfc : sum_form_comp) : sum_form_comp :=
⟨sfc.sf.scale (-1), sfc.c.reverse⟩-/

/--
 This is only valid for positive m
-/
meta def sum_form_comp.scale (m : ℚ) : sum_form_comp → sum_form_comp
| ⟨sf, c⟩ := ⟨sf.scale m, c⟩

meta def sum_form_comp.of_ineq_data {lhs rhs} (id : ineq_data lhs rhs) : sum_form_comp :=
match id.inq.to_slope, spec_comp_and_flipped_of_comp id.inq.to_comp with
| slope.horiz, (cmp, flp) := ⟨if flp then (sum_form.of_expr rhs).negate else sum_form.of_expr rhs, cmp⟩
| slope.some m, (cmp, flp) := 
   let nsfc := (sum_form.of_expr lhs).add_factor (sum_form.of_expr rhs) (-m) in
   ⟨if flp then nsfc.negate else nsfc, cmp⟩
end

meta def sum_form_comp.of_ineq_proof {lhs rhs id} (ip : ineq_proof lhs rhs id) : sum_form_comp :=
sum_form_comp.of_ineq_data ⟨_, ip⟩

  
-- some of these are unused
meta inductive sum_form_proof : sum_form_comp → Type
| of_ineq_proof : Π {lhs rhs iq}, Π id : ineq_proof lhs rhs iq,
    sum_form_proof (sum_form_comp.of_ineq_proof id)
| of_add_factor_same_comp : Π {lhs rhs c1 c2}, Π m : ℚ, -- assumes m is positive
  sum_form_proof ⟨lhs, c1⟩ → sum_form_proof ⟨rhs, c2⟩ → sum_form_proof ⟨lhs.add_factor rhs m, spec_comp.strongest c1 c2⟩ 
--| of_add_factor_rev_comp : Π {lhs rhs c1 c2}, Π m : ℚ, -- assumes m is negative
--  sum_form_proof ⟨lhs, c1⟩ → sum_form_proof ⟨rhs, c2⟩ → sum_form_proof ⟨lhs.add_factor rhs m, spec_comp.strongest c1 c2.reverse⟩ 
/-| of_add_factor_eq : Π {lhs rhs c}, Π m : ℚ, 
  sum_form_proof ⟨lhs, c⟩ → sum_form_proof ⟨rhs, gen_comp.eq⟩ → sum_form_proof ⟨lhs.add_factor rhs m, c⟩ -/
--| of_reverse : Π {sfc}, sum_form_proof sfc → sum_form_proof (sfc.reverse)
| of_scale : Π {sfc}, Π m, sum_form_proof sfc → sum_form_proof (sfc.scale m)
| fake : Π sd, sum_form_proof sd

meta structure sum_form_comp_data :=
(sfc : sum_form_comp) (prf : sum_form_proof sfc)

meta def sum_form_comp_data.of_ineq_data {lhs rhs} (id : ineq_data lhs rhs) : sum_form_comp_data :=
⟨_, sum_form_proof.of_ineq_proof id.prf⟩

meta def sum_form_comp_data.vars (sfcd : sum_form_comp_data) : list expr :=
sfcd.sfc.sf.keys

-- assumes lhs < rhs as exprs. cl*lhs + cr*rhs R 0 ==> ineq_data
meta def mk_ineq_data_of_lhs_rhs (lhs rhs : expr) (cl cr : ℚ) (c : comp) : Σ l r, ineq_data l r :=
let c' := if cl > 0 then c else c.reverse,
    iq := ineq.of_comp_and_slope (c') (slope.some (-cr/cl)) in
⟨lhs, rhs, ⟨iq, ineq_proof.hyp _ _ _ ```(0)⟩⟩ -- TODO


-- we need a proof constructor for ineq and eq
meta def sum_form_comp_data.to_ineq_data : sum_form_comp_data → option (Σ lhs rhs, ineq_data lhs rhs) 
| ⟨⟨sf, spec_comp.eq⟩, prf⟩ := none
| ⟨sfc, prf⟩ := 
  match sfc.sf.get_nonzero_factors with
  | [(rhs, cr), (lhs, cl)] := 
    if lhs.lt rhs then mk_ineq_data_of_lhs_rhs lhs rhs cl cr (sfc.c.to_comp)
    else mk_ineq_data_of_lhs_rhs rhs lhs cr cl (sfc.c.to_comp)
  | _ := none
  end

meta def sum_form_comp_data.to_eq_data : sum_form_comp_data → option (Σ lhs rhs, eq_data lhs rhs)
| ⟨⟨sf, spec_comp.eq⟩, prf⟩ :=
  match sf.get_nonzero_factors with
  | [(rhs, cr), (lhs, cl)] := some ⟨lhs, rhs, ⟨(-cr/cl), eq_proof.hyp _ _ _ ```(0)⟩⟩ -- TODO
  | _ := none
  end
| _ := none
  

meta instance sum_form_comp.has_to_format : has_to_format sum_form_comp :=
⟨λ sfc, "{" ++ to_fmt (sfc.sf) ++ to_fmt sfc.c ++ "0}"⟩

meta instance sum_form_data.has_to_format : has_to_format sum_form_comp_data :=
⟨λ sfcd, to_fmt sfcd.sfc⟩


/-meta def sum_form_comp_data.reverse (sfcd : sum_form_comp_data) : sum_form_comp_data :=
⟨_, sum_form_proof.of_reverse sfcd.prf⟩-/

meta def sum_form_comp_data.get_coeff (sfcd : sum_form_comp_data) (e : expr) : ℚ :=
sfcd.sfc.sf.get_coeff e

meta def sum_form.normalize (sf : sum_form) : sum_form :=
match rb_map.to_list sf with
| [] := sf
| (_, m)::t := if abs m = 1 then sf else sf.scale (abs (1/m))
end

meta def sum_form.is_normalized (sd : sum_form) : bool :=
match rb_map.to_list sd with
| [] := tt
| (_, m)::t := abs m = 1
end

meta def sum_form_comp.normalize : sum_form_comp → sum_form_comp
| ⟨sf, c⟩ := ⟨sf.normalize, c⟩

meta def sum_form_comp.is_normalized : sum_form_comp → bool
| ⟨sf, _⟩ := sf.is_normalized

meta def sum_form_comp_data.normalize (sd : sum_form_comp_data) : sum_form_comp_data :=
match rb_map.to_list sd.sfc.sf with
| [] := sd
| (_, m)::t := if abs m = 1 then sd else ⟨_, sum_form_proof.of_scale (abs (1/m)) sd.prf⟩
end

meta def sum_form_comp_data.is_normalized : sum_form_comp_data → bool
| ⟨sfc, _⟩ := sfc.is_normalized

/--- assumes sfc2.c is gen_comp.eq, and the coeff of pvt in both is nonzero
meta def sum_form_comp_data.elim_expr_using_eq (sfd1 : sum_form_comp_data) : sum_form_comp_data → expr → 
     option sum_form_comp_data
| ⟨⟨sf2, gen_comp.eq⟩, prf⟩ pvt := 
let cf1 := sfd1.get_coeff pvt,
    cf2 := sf2.get_coeff pvt in
have h : sfd1.sfc = {sf := sfd1.sfc.sf, c := sfd1.sfc.c}, by congr_struct,
some ⟨_, sum_form_proof.of_add_factor_eq  (-cf1/cf2) (by rw -h; apply sfd1.prf) prf⟩
| _ _ := none-/


-- assumes the coeff of pvt in both is nonzero
meta def sum_form_comp_data.elim_expr_aux : sum_form_comp_data → sum_form_comp_data → expr → 
     option sum_form_comp_data
| ⟨⟨sf1, c1⟩, prf1⟩ ⟨⟨sf2, c2⟩, prf2⟩ pvt := 
let cf1 := sf1.get_coeff pvt,
    cf2 := sf2.get_coeff pvt,
    fac := (-cf1/cf2) in
if (fac > 0) then
  some ⟨_, sum_form_proof.of_add_factor_same_comp fac prf1 prf2⟩
--else if (fac < 0) ∧ (c1.dir * c2.dir ≤ 0) then
--  some ⟨_, sum_form_proof.of_add_factor_rev_comp fac prf1 prf2⟩
else none

meta def sum_form_comp_data.elim_expr (sfcd1 sfcd2 : sum_form_comp_data) (pvt : expr) : option sum_form_comp_data :=
if sfcd1.get_coeff pvt = 0 then some sfcd1
else if sfcd2.get_coeff pvt = 0 then none
else sum_form_comp_data.elim_expr_aux sfcd1 sfcd2 pvt

private meta def compare_coeffs (sf1 sf2 : sum_form) (h : expr) : ordering :=
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

meta def sum_form_comp_data.order : sum_form_comp_data → sum_form_comp_data → ordering
| ⟨sfc1, _⟩ ⟨sfc2, _⟩ := sfc1.order sfc2

-- this is a crazy hack.
/-meta def sum_form_comp_data.order :=
λ c1 c2 : sum_form_comp_data, has_ordering.cmp ((to_fmt c1).to_string options.mk).to_name ((to_fmt c2).to_string options.mk).to_name
-/
 

meta instance : has_ordering sum_form_comp_data := 
⟨sum_form_comp_data.order⟩

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
cmps.fold mk_rb_set (λ c rv, elim_expr_from_comp_data c cmps (trace_val e) rv)

/--
 Performs all possible eliminations with sfcd on cmps. Returns a set of all new comps, NOT including the old ones.
-/
meta def new_exprs_from_comp_data_set (sfcd : sum_form_comp_data) (cmps : rb_set sum_form_comp_data) : rb_set sum_form_comp_data :=
sfcd.vars.foldr (λ e rv, elim_expr_from_comp_data sfcd cmps e rv) mk_rb_set

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

meta def elim_list_into_set : rb_set sum_form_comp_data → list sum_form_comp_data → rb_set sum_form_comp_data
| cmps [] := cmps
| cmps (sfcd::new_cmps) :=
   if (trace_val (cmps.contains (trace_val sfcd)) : bool) then elim_list_into_set cmps new_cmps else
   let new_gen := (new_exprs_from_comp_data_set sfcd.normalize cmps).keys in
   elim_list_into_set (cmps.insert sfcd) (new_cmps.append new_gen)

meta def elim_list (cmps : list sum_form_comp_data) : list sum_form_comp_data :=
(elim_list_into_set mk_rb_set cmps).to_list

end polya

section tests

variables x y z : ℚ
meta def x' := ```(x)
meta def y' := ```(y)
meta def z' := ```(z)

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

meta def d1 : sum_form_comp_data := ⟨c1, sum_form_proof.fake _⟩
meta def d2 : sum_form_comp_data := ⟨c2, sum_form_proof.fake _⟩
meta def d3 : sum_form_comp_data := ⟨c3, sum_form_proof.fake _⟩
meta def d4 : sum_form_comp_data := ⟨c4, sum_form_proof.fake _⟩
meta def d5 : sum_form_comp_data := ⟨c5, sum_form_proof.fake _⟩
meta def d6 : sum_form_comp_data := ⟨c6, sum_form_proof.fake _⟩

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


#exit
run_cmd trace $
elim_list  [d1, d3, d5] --[d1, d3,  d5, d6]

end tests
