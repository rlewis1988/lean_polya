import .proof

namespace polya
open native

/-
DATA OBJECTS
-/

open native
meta structure ineq_data (lhs rhs : expr) :=
(inq : ineq)
(prf : ineq_proof lhs rhs inq)

namespace ineq_data
meta def reverse {lhs rhs : expr} (id : ineq_data lhs rhs) : ineq_data rhs lhs :=
if id.inq.is_horiz then
 let sp := sign_proof.ineq_rhs id.inq.to_comp/-.reverse-/ id.prf in
  ⟨_, ineq_proof.zero_comp_of_sign_proof lhs id.inq.reverse sp⟩
else if id.inq.is_zero_slope then
 let sp := sign_proof.ineq_lhs id.inq.to_comp id.prf in
  ⟨_, ineq_proof.horiz_of_sign_proof rhs id.inq.reverse sp⟩
else
 ⟨id.inq.reverse, id.prf.sym⟩

meta def to_format {lhs rhs} : ineq_data lhs rhs → format
| ⟨inq, prf⟩ := "⟨" ++ to_fmt inq ++ " : " ++ to_fmt prf ++ "⟩"

meta instance has_to_format (lhs rhs) : has_to_format (ineq_data lhs rhs) :=
⟨to_format⟩

/-meta instance has_decidable_eq (lhs rhs) : decidable_eq (ineq_data lhs rhs) :=
by tactic.mk_dec_eq_instance-/

/- meta def to_expr {lhs rhs} (id : ineq_data lhs rhs) : tactic expr :=
id.inq.to_expr lhs rhs -/
end ineq_data

meta structure eq_data (lhs rhs : expr) :=
(c   : ℚ)
(prf : eq_proof lhs rhs c)

namespace eq_data
meta def refl (e : expr) : eq_data e e :=
⟨1, eq_proof.adhoc e e 1 (do s ← to_string <$> tactic.pp e, return ⟨s ++ " = " ++ s, "reflexivity", []⟩) $ do (_, pr) ← tactic.solve_aux `(%%e = (1 : ℚ) * %%e) `[simp only [one_mul]], return pr⟩

meta def reverse {lhs rhs : expr} (ei : eq_data lhs rhs) : eq_data rhs lhs :=
⟨(1/ei.c), ei.prf.sym⟩

meta def implies_ineq {lhs rhs} (ed : eq_data lhs rhs) (id : ineq) : bool :=
match id.to_slope with
| slope.some c := (c = ed.c) && bnot (id.strict)
| horiz        := ff
end

meta def to_format {lhs rhs} : eq_data lhs rhs → format
| ⟨c, prf⟩ := "⟨(lhs)=" ++ to_fmt c ++ "*(rhs)⟩" 

meta instance has_to_format (lhs rhs) : has_to_format (eq_data lhs rhs) :=
⟨eq_data.to_format⟩
end eq_data

meta structure diseq_data (lhs rhs : expr) :=
(c : ℚ)
(prf : diseq_proof lhs rhs c)

namespace diseq_data
meta def reverse {lhs rhs : expr} (di : diseq_data lhs rhs) : diseq_data rhs lhs :=
⟨(1/di.c), di.prf.sym⟩
end diseq_data

meta structure sign_data (e : expr) :=
(c : gen_comp)
(prf : sign_proof e c)

namespace sign_data
meta def to_format {e} : sign_data e → format
| ⟨c, _⟩ := to_fmt "{" ++ to_fmt e ++ to_fmt c ++ to_fmt "0}"

meta instance has_to_format {e} : has_to_format (sign_data e) :=
⟨to_format⟩ 
end sign_data


meta structure sum_form_comp_data :=
(sfc : sum_form_comp) (prf : sum_form_proof sfc) (elim_list : rb_set expr)

namespace sum_form_comp_data

-- TODO: do we need to take elim_vars into account for this order?
meta def sum_form_comp_data.order : sum_form_comp_data → sum_form_comp_data → ordering
| ⟨sfc1, _, _⟩ ⟨sfc2, _, _⟩ := sfc1.order sfc2

meta instance : has_lt sum_form_comp_data := ⟨λ x y, sum_form_comp_data.order x y = ordering.lt⟩
meta instance : decidable_rel (@has_lt.lt sum_form_comp_data _) := λ _ _, by apply_instance

meta def of_ineq_data {lhs rhs} (id : ineq_data lhs rhs) : sum_form_comp_data :=
⟨_, sum_form_proof.of_ineq_proof id.prf, mk_rb_set⟩

meta def of_eq_data {lhs rhs} (ed : eq_data lhs rhs) : sum_form_comp_data :=
⟨_, sum_form_proof.of_eq_proof ed.prf, mk_rb_set⟩

meta def of_sign_data {e} (sd : sign_data e) : sum_form_comp_data :=
⟨_, sum_form_proof.of_sign_proof sd.prf, mk_rb_set⟩

meta def vars (sfcd : sum_form_comp_data) : list expr :=
sfcd.sfc.sf.keys

meta instance has_to_format : has_to_format sum_form_comp_data :=
⟨λ sfcd, to_fmt sfcd.sfc⟩

meta def get_coeff (sfcd : sum_form_comp_data) (e : expr) : ℚ :=
sfcd.sfc.sf.get_coeff e


meta def normalize (sd : sum_form_comp_data) : sum_form_comp_data :=
match rb_map.to_list sd.sfc.sf with
| [] := sd
| (_, m)::t := if abs m = 1 then sd else ⟨_, sum_form_proof.of_scale (abs (1/m)) sd.prf, sd.elim_list⟩
end

meta def is_normalized : sum_form_comp_data → bool
| ⟨sfc, _, _⟩ := sfc.is_normalized


meta def is_contr : sum_form_comp_data → bool
| ⟨sfc, _, _⟩ := sfc.is_contr

end sum_form_comp_data


meta structure prod_form_comp_data :=
(pfc : prod_form_comp) (prf : prod_form_proof pfc) (elim_list : rb_set expr)
namespace prod_form_comp_data

meta def vars (pfcd : prod_form_comp_data) : list expr :=
pfcd.pfc.pf.exps.keys

meta def of_ineq_data {lhs rhs cl cr} (id : ineq_data lhs rhs) (spl : sign_proof lhs cl) (spr : sign_proof rhs cr) : prod_form_comp_data :=
⟨_, prod_form_proof.of_ineq_proof id.prf spl spr, mk_rb_set⟩

meta def of_eq_data {lhs rhs} (ed : eq_data lhs rhs) (sp : sign_proof lhs gen_comp.ne) : prod_form_comp_data :=
⟨_, prod_form_proof.of_eq_proof ed.prf sp, mk_rb_set⟩

meta instance has_to_format : has_to_format prod_form_comp_data :=
⟨λ sfcd, to_fmt sfcd.pfc⟩

end prod_form_comp_data

/-
INFO OBJECTS
-/

/--
 In the two_comps case, we maintain the invariant that the defining ray of the first is 
 counterclockwise to that of the second.
-/
meta inductive ineq_info (lhs rhs : expr)
| no_comps {}  : ineq_info
| one_comp     : ineq_data lhs rhs → ineq_info
| two_comps    : ineq_data lhs rhs → ineq_data lhs rhs → ineq_info
| equal        : eq_data lhs rhs → ineq_info

namespace ineq_info
meta def data {lhs rhs} : ineq_info lhs rhs → list (ineq_data lhs rhs)
| no_comps := []
| (one_comp id) := [id]
| (two_comps id1 id2) := [id1, id2]
| (equal _) := []

meta def mk_two_comps {lhs rhs} (id1 id2 : ineq_data lhs rhs) : ineq_info lhs rhs :=
if id2.inq.clockwise_of id1.inq then two_comps id1 id2 else two_comps id2 id1

meta instance inhabited (lhs rhs) : inhabited (ineq_info lhs rhs) :=
⟨no_comps⟩

meta def reverse {lhs rhs : expr} : ineq_info lhs rhs → ineq_info rhs lhs
| no_comps            := no_comps
| (one_comp id1)      := one_comp id1.reverse
| (two_comps id1 id2) := ineq_info.mk_two_comps id1.reverse id2.reverse
| (equal ed)          := equal ed.reverse

meta def to_format {lhs rhs} : ineq_info lhs rhs → format
| no_comps := "ineq_info.empty"
| (one_comp id1) := "{" ++ to_fmt id1 ++ "}"
| (two_comps id1 id2) := "{" ++ to_fmt id1 ++ " | " ++ to_fmt id2 ++ "}"
| (equal ed) := "{" ++ to_fmt ed ++ "}"

meta instance has_to_format (lhs rhs) : has_to_format (ineq_info lhs rhs) :=
⟨to_format⟩

meta def implies_ineq {lhs rhs : expr} : ineq_info lhs rhs → ineq → bool
| (one_comp ⟨inq1, _⟩) ninq := inq1.implies ninq
| (two_comps ⟨inq1, _⟩ ⟨inq2, _⟩) ninq := ineq.two_imply inq1 inq2 ninq
| (equal ed) ninq := ed.implies_ineq ninq
| _ _ := ff

meta def implies_eq {lhs rhs : expr} : ineq_info lhs rhs → ℚ → bool
| (equal ed) m := ed.c = m
| _ _ := ff
end ineq_info

meta def diseq_info (lhs rhs : expr) :=
rb_map ℚ (diseq_data lhs rhs)

namespace diseq_info
meta instance inhabited (lhs rhs) : inhabited (diseq_info lhs rhs) :=
⟨mk_rb_map⟩

meta def reverse {lhs rhs : expr} : diseq_info lhs rhs → diseq_info rhs lhs :=
rb_map.map diseq_data.reverse
end diseq_info

meta def sign_info (e : expr) :=
option (sign_data e)

namespace sign_info
meta def is_strict {e : expr} : sign_info e → bool
| (some sd) := sd.c.is_strict
| none := ff

meta instance inhabited (lhs) : inhabited (sign_info lhs) :=
⟨none⟩

--renamed from comp_option_of_sign_info
--TODO: make private?
meta def to_option_comp {e} : sign_info e → option gen_comp
| (some c) := c.c
| none := none
end sign_info

--TODO: move this up in the ineq_info namespace?
section two_var_ineqs
meta def ineq_info.implies {lhs rhs : expr} (ii : ineq_info lhs rhs) (id : ineq_data lhs rhs) : bool :=
ii.implies_ineq id.inq
end two_var_ineqs

-- id.x ≥ 0, id.strict
private meta def mk_cmp_aux : bool → bool → gen_comp
| tt tt := gen_comp.gt
| tt ff := gen_comp.ge
| ff tt := gen_comp.lt
| ff ff := gen_comp.le

-- assumes id.to_slope = slope.horiz
meta def eq_data.get_implied_sign_info_from_horiz_ineq {lhs rhs} (ed : eq_data lhs rhs) :
     ineq_data lhs rhs → sign_info lhs × sign_info rhs | ⟨id, prf⟩ := 
if ed.c > 0 then
  let cmp := mk_cmp_aux (id.x ≥ 0) id.strict,
      pr1 := sign_proof.ineq_of_eq_and_ineq_lhs cmp ed.prf prf,
      pr2 := sign_proof.ineq_rhs cmp prf in
  (some ⟨_, pr1⟩, some ⟨_, pr2⟩)
else if h : ed.c = 0 then
  let pr1 := sign_proof.eq_of_eq_zero (by rw ←h; apply ed.prf),
      pr2 := sign_proof.ineq_rhs (mk_cmp_aux (id.x ≥ 0) id.strict) prf in
  (some ⟨_, pr1⟩, some ⟨_, pr2⟩)
else 
  let cmp := mk_cmp_aux (id.x ≤ 0) id.strict,
      pr1 := sign_proof.ineq_of_eq_and_ineq_lhs cmp ed.prf prf,
      pr2 := sign_proof.ineq_rhs cmp.reverse prf in
  (some ⟨_, pr1⟩, some ⟨_, pr2⟩)

-- assumes id.to_slope = slope.some m, with m ≠ ed.c
meta def eq_data.get_implied_sign_info_from_slope_ineq {lhs rhs} (ed : eq_data lhs rhs) (m : ℚ) :
     ineq_data lhs rhs → sign_info lhs × sign_info rhs | ⟨id, prf⟩ := 
let cmp  := if m - ed.c < 0 then id.to_comp else id.to_comp.reverse in 
if ed.c > 0 then 
  let pr1 := sign_proof.ineq_of_eq_and_ineq_lhs cmp ed.prf prf,
      pr2 := sign_proof.ineq_of_eq_and_ineq_rhs cmp ed.prf prf in
      (some ⟨_, pr1⟩, some ⟨_, pr2⟩)
else if h : ed.c = 0 then
  let pr1 := sign_proof.eq_of_eq_zero (by rw ←h; apply ed.prf),
      pr2 := sign_proof.ineq_of_ineq_and_eq_zero_rhs cmp prf pr1 in
      (some ⟨_, pr1⟩, some ⟨_, pr2⟩)
else
  let pr1 := sign_proof.ineq_of_eq_and_ineq_lhs cmp.reverse ed.prf prf,
      pr2 := sign_proof.ineq_of_eq_and_ineq_rhs cmp ed.prf prf in
      (some ⟨_, pr1⟩, some ⟨_, pr2⟩)


meta def eq_data.get_implied_sign_info_from_ineq {lhs rhs} (ed : eq_data lhs rhs) 
     (id : ineq_data lhs rhs) : sign_info lhs × sign_info rhs  := 
match id.inq.to_slope with
| slope.horiz := ed.get_implied_sign_info_from_horiz_ineq id
| slope.some m := 
  if m = ed.c then (none, none)
  else ed.get_implied_sign_info_from_slope_ineq m id
end

meta def eq_data.implies_ineq_with_sign_info {lhs rhs} (ed : eq_data lhs rhs) (iq : ineq) 
     (sil : sign_info lhs) (sir : sign_info rhs) : bool :=
match point_of_coeff_and_comps ed.c sil.to_option_comp sir.to_option_comp with
| some (x, y) := (iq.clockwise_of ⟨tt, x, y⟩ && ((bnot iq.strict) || sil.is_strict || sir.is_strict)) 
                  || ed.implies_ineq iq
| none := ff
end

meta def ineq_data.strengthen_from_diseq {lhs rhs} (id : ineq_data lhs rhs) (dd : diseq_data lhs rhs) :
         ineq_data lhs rhs :=
if id.inq.strict then id else
match id.inq.to_slope with
| slope.horiz  := id
| slope.some m := 
    if m = dd.c then 
    ⟨id.inq.strengthen, ineq_proof.of_ineq_proof_and_diseq id.prf dd.prf⟩ 
    else id
end

meta def ineq_data.strengthen_from_sign_lhs {lhs rhs} (id : ineq_data lhs rhs) (dd : sign_data lhs) :
         ineq_data lhs rhs :=
if id.inq.strict || bnot (dd.c = gen_comp.ne) then id else
match id.inq.to_slope with
| slope.horiz := id
| slope.some m :=
    if (m = 0) then 
    ⟨id.inq.strengthen, ineq_proof.of_ineq_proof_and_sign_lhs id.prf dd.prf⟩ 
    else id
end

meta def ineq_data.strengthen_from_sign_rhs {lhs rhs} (id : ineq_data lhs rhs) (dd : sign_data rhs) :
         ineq_data lhs rhs :=
if id.inq.strict || bnot (dd.c = gen_comp.ne) then id else
match id.inq.to_slope with
| slope.horiz := ⟨id.inq.strengthen, ineq_proof.of_ineq_proof_and_sign_rhs id.prf dd.prf⟩
| slope.some m := id
end

end polya
