import .datatypes .struct_eta

namespace polya

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
sf.map (λ q, c*q)

meta def sum_form.sub (lhs rhs : sum_form) : sum_form :=
lhs.add (rhs.scale (-1))

meta instance : has_add sum_form := ⟨sum_form.add⟩
meta instance : has_sub sum_form := ⟨sum_form.sub⟩

meta def sum_form.add_factor (lhs rhs : sum_form) (c : ℚ) : sum_form :=
lhs + (rhs.scale c)

meta structure sum_form_comp :=
(sf : sum_form) (c : gen_comp) 

meta def sum_form_comp.reverse (sfc : sum_form_comp) : sum_form_comp :=
⟨sfc.sf.scale (-1), sfc.c.reverse⟩

meta def sum_form_comp.scale (m : ℚ) : sum_form_comp → sum_form_comp
| ⟨sf, c⟩ := ⟨sf.scale m, if m ≥ 0 then c else c.reverse⟩

meta def sum_form_comp.of_ineq_data {lhs rhs} (id : ineq_data lhs rhs) : sum_form_comp :=
match id.inq.to_slope with
| slope.horiz := ⟨sum_form.of_expr rhs, id.inq.to_comp⟩
| slope.some m := ⟨(sum_form.of_expr lhs).add_factor (sum_form.of_expr rhs) (-m), id.inq.to_comp⟩
end

meta def sum_form_comp.of_ineq_proof {lhs rhs id} (ip : ineq_proof lhs rhs id) : sum_form_comp :=
sum_form_comp.of_ineq_data ⟨_, ip⟩

-- we need a proof constructor for ineq and eq
meta def sum_form_comp.to_ineq_data (sfc : sum_form_comp) : option Σ lhs rhs, ineq_data lhs rhs :=
if (sfc.c.dir = 0) then none else
match sfc.sf.get_nonzero_factors with
| [(rhs, cr), (lhs, cl)] := 
  let iq := ineq.of_comp_and_slope (sfc.c.to_comp) (slope.some (-cr/cl)) in
  some ⟨lhs, rhs, ⟨iq, sorry⟩⟩
| _ := none
end

meta def sum_form_comp.to_eq_data (sfc : sum_form_comp) : option Σ lhs rhs, eq_data lhs rhs :=
if bnot (sfc.c = gen_comp.eq) then none else
match sfc.sf.get_nonzero_factors with
| [(rhs, cr), (lhs, cl)] := some ⟨lhs, rhs, ⟨(-cr/cl), sorry⟩⟩
| _ := none
end
  
  
-- some of these are unused
meta inductive sum_form_proof : sum_form_comp → Type
| of_ineq_proof : Π {lhs rhs iq}, Π id : ineq_proof lhs rhs iq,
    sum_form_proof (sum_form_comp.of_ineq_proof id)
| of_add_factor_same_comp : Π {lhs rhs c1 c2}, Π m : ℚ, -- assumes m is positive
  sum_form_proof ⟨lhs, c1⟩ → sum_form_proof ⟨rhs, c2⟩ → sum_form_proof ⟨lhs.add_factor rhs m, gen_comp.strongest c1 c2⟩ 
| of_add_factor_rev_comp : Π {lhs rhs c1 c2}, Π m : ℚ, -- assumes m is negative
  sum_form_proof ⟨lhs, c1⟩ → sum_form_proof ⟨rhs, c2⟩ → sum_form_proof ⟨lhs.add_factor rhs m, gen_comp.strongest c1 c2.reverse⟩ 
/-| of_add_factor_eq : Π {lhs rhs c}, Π m : ℚ, 
  sum_form_proof ⟨lhs, c⟩ → sum_form_proof ⟨rhs, gen_comp.eq⟩ → sum_form_proof ⟨lhs.add_factor rhs m, c⟩ -/
| of_reverse : Π {sfc}, sum_form_proof sfc → sum_form_proof (sfc.reverse)
| of_scale : Π {sfc}, Π m, sum_form_proof sfc → sum_form_proof (sfc.scale m)
| fake : Π sd, sum_form_proof sd

meta structure sum_form_comp_data :=
(sfc : sum_form_comp) (prf : sum_form_proof sfc)


meta instance sum_form_comp.has_to_format : has_to_format sum_form_comp :=
⟨λ sfc, "{" ++ to_fmt (sfc.sf) ++ to_fmt sfc.c ++ "0}"⟩

meta instance sum_form_data.has_to_format : has_to_format sum_form_comp_data :=
⟨λ sfcd, to_fmt sfcd.sfc⟩


meta def sum_form_comp_data.reverse (sfcd : sum_form_comp_data) : sum_form_comp_data :=
⟨_, sum_form_proof.of_reverse sfcd.prf⟩

meta def sum_form_comp_data.get_coeff (sfcd : sum_form_comp_data) (e : expr) : ℚ :=
sfcd.sfc.sf.get_coeff e

meta def sum_form_comp_data.normalize (sd : sum_form_comp_data) : sum_form_comp_data :=
match rb_map.to_list sd.sfc.sf with
| [] := sd
| (_, m)::t := ⟨_, sum_form_proof.of_scale (1/m) sd.prf⟩
end


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
if (fac > 0) ∧ (c1.dir * c2.dir ≥ 0) then
  some ⟨_, sum_form_proof.of_add_factor_same_comp fac prf1 prf2⟩
else if (fac < 0) ∧ (c1.dir * c2.dir ≤ 0) then
  some ⟨_, sum_form_proof.of_add_factor_rev_comp fac prf1 prf2⟩
else none

meta def sum_form_comp_data.elim_expr (sfcd1 sfcd2 : sum_form_comp_data) (pvt : expr) : option sum_form_comp_data :=
if sfcd1.get_coeff pvt = 0 then some sfcd1
else if sfcd2.get_coeff pvt = 0 then none
else sum_form_comp_data.elim_expr_aux sfcd1 sfcd2 pvt


-- this is a crazy hack.
meta def sum_form_comp_data.order :=
λ c1 c2 : sum_form_comp_data, has_ordering.cmp ((to_fmt c1).to_string options.mk).to_name ((to_fmt c2).to_string options.mk).to_name
 

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

meta def elim_expr_from_comp_data (sfcd : sum_form_comp_data) (cmps : rb_set sum_form_comp_data) 
         (e : expr) (rv : rb_set sum_form_comp_data) : rb_set sum_form_comp_data :=
cmps.fold rv (λ c rv', sfcd.elim_into c e rv')

meta def elim_expr_from_comp_data_set (cmps : rb_set sum_form_comp_data) (e : expr) : rb_set sum_form_comp_data :=
cmps.fold mk_rb_set (λ c rv, elim_expr_from_comp_data c cmps e rv)

meta def elim_expr_from_comp_data_list (cmps : list sum_form_comp_data) (e : expr) : list sum_form_comp_data :=
(elim_expr_from_comp_data_set (rb_set.of_list cmps) e).to_list


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

meta def c1 : sum_form_comp := ⟨e1, gen_comp.le⟩ -- 3x + 2y + z ≤ 0
meta def c2 : sum_form_comp := ⟨e2, gen_comp.gt⟩
meta def c3 : sum_form_comp := ⟨e3, gen_comp.ge⟩
meta def c4 : sum_form_comp := ⟨e4, gen_comp.eq⟩
meta def c5 : sum_form_comp := ⟨e5, gen_comp.gt⟩
meta def c6 : sum_form_comp := ⟨e6, gen_comp.lt⟩

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

end tests
