import data.hash_map .rat_additions

instance : has_ordering ℚ :=
⟨λ a b, if a = b then ordering.eq else if a < b then ordering.lt else ordering.gt⟩

namespace hash_map
def {u v} find' {α : Type u} {β : α → Type v} [decidable_eq α] (m : hash_map α β) (a : α) [inhabited (β a)] : β a :=
match m.find a with
| none := default _
| some b := b
end

end hash_map

namespace polya

inductive comp
| le | lt | ge | gt

inductive gen_comp
| le | lt | ge | gt | eq | ne

namespace comp
instance : decidable_eq comp := by tactic.mk_dec_eq_instance

def reverse : comp → comp
| le := ge
| lt := gt
| ge := le
| gt := lt

def negate : comp → comp
| le := gt
| lt := ge
| ge := lt
| gt := le

def strengthen : comp → comp
| le := lt
| ge := gt
| a  := a

def is_strict : comp → bool
| lt := tt
| gt := tt
| _  := ff

def is_less : comp → bool
| lt := tt
| le := tt
| _  := ff

def implies (c1 c2 : comp) : bool :=
(is_less c1 = is_less c2) && (is_strict c1 || bnot (is_strict c2))

meta def to_format : comp → format
| le := "≤"
| lt := "<"
| ge := "≥"
| gt := ">"

meta def to_gen_comp : comp → gen_comp
| le := gen_comp.le
| lt := gen_comp.lt
| ge := gen_comp.ge
| gt := gen_comp.gt

meta instance : has_coe comp gen_comp :=
⟨to_gen_comp⟩ 

meta instance : has_to_format comp :=
⟨to_format⟩

end comp

namespace gen_comp
instance : decidable_eq gen_comp := by tactic.mk_dec_eq_instance

def dir : gen_comp → ℤ
| le := -1
| lt := -1
| ge := 1
| gt := 1
| eq := 0
| ne := 0


def reverse : gen_comp → gen_comp
| le := ge
| lt := gt
| ge := le
| gt := lt
| eq := ne
| ne := eq

def is_strict : gen_comp → bool
| lt := tt
| gt := tt
| _  := ff

def is_less : gen_comp → bool
| lt := tt
| le := tt
| _  := ff

def is_ineq : gen_comp → bool
| eq := ff
| ne := ff
| _  := tt

def implies_aux : gen_comp → gen_comp → bool
| lt le := tt
| gt ge := tt
| eq le := tt
| eq ge := tt
| lt ne := tt
| gt ne := tt
| _ _   := ff

def implies (c1 c2 : gen_comp) : bool :=
(c1 = c2) || implies_aux c1 c2 


meta def to_format : gen_comp → format
| le := "≤"
| lt := "<"
| ge := "≥"
| gt := ">"
| eq := "="
| ne := "≠"

meta instance : has_to_format gen_comp :=
⟨to_format⟩

end gen_comp

/--
 This does not represent the traditional slope, but (x/y) if (x, y) is a point on the line
-/
inductive slope
| horiz : slope
| some : rat → slope

instance slope.decidable_eq : decidable_eq slope := by tactic.mk_dec_eq_instance

/--
 An inequality (str, a, b) represents the halfplane counterclockwise from the vector (a, b).
 If str is true, it is strict (ie, it doesn't include the line bx-ay=0).
-/
structure ineq :=
(strict : bool)
(x y : ℚ)

namespace ineq
instance : inhabited ineq :=
⟨⟨ff, 1, 0⟩⟩

/-meta instance rat.has_to_format : has_to_format ℚ :=
⟨λ q, ↑"0"⟩-/

open comp slope
def to_comp (i : ineq) : comp := -- DOUBLE CHECK THIS
if i.x ≥ 0 then
  if i.y > 0 then
    if i.strict then lt else le
  else 
    if i.strict then gt else ge
else
  if i.y > 0 then
    if i.strict then lt else le
  else
    if i.strict then gt else ge

def to_slope (i : ineq) : slope :=
if i.y = 0 then slope.horiz else slope.some (i.x / i.y) 

meta def to_format (inq : ineq) : format :=
let cf := to_fmt inq.to_comp in
match inq.to_slope with
| slope.horiz := "(rhs)" ++ cf ++ "0"
| slope.some c := if c = 0 then "(lhs)" ++ cf ++ "0" else
"(lhs) " ++ cf ++ to_fmt c ++ "(rhs)"
end

meta instance ineq.has_to_format : has_to_format ineq :=
⟨to_format⟩

def equiv (i1 i2 : ineq) : bool :=
to_slope i1 = to_slope i2

def of_comp_and_slope (c : comp) : slope → ineq
| horiz    := if is_less c then ⟨is_strict c, -1, 0⟩ else ⟨is_strict c, 1, 0⟩
| (some v) :=
  if v > 0 then 
    if is_less c then ⟨is_strict c, v, 1⟩ else ⟨is_strict c, -v, -1⟩
  else
    if is_less c then ⟨is_strict c, v, 1⟩ else ⟨is_strict c, -v, -1⟩


/--
 Turns a < 3b into a > 3b
-/
def flip (i : ineq) : ineq :=
⟨i.strict, -i.x, -i.y⟩

/--
 Turns a < 3b into a ≥ 3b
-/
def negate (i : ineq) : ineq :=
⟨bnot i.strict, -i.x, -i.y⟩

/--
 Turns a < 3b into b > 1/3 a.
 This is equivalent to reflecting over the identity line and flipping
-/
def reverse (i : ineq) : ineq :=
⟨i.strict, -i.y, -i.x⟩

/--
 Turns a ≤ 3b into a < 3b.
-/
def strengthen (i : ineq) : ineq :=
{i with strict := tt}

def same_quadrant (i1 i2 : ineq) : bool :=
(i1.x > 0 ↔ i2.x > 0) && (i1.y > 0 ↔ i2.y > 0)

def implies (i1 i2 : ineq) : bool :=
(i1.to_slope = i2.to_slope) && (same_quadrant i1 i2) && (i1.strict || bnot (i2.strict))


def clockwise_of (i1 i2 : ineq) : bool :=
i1.x*i2.y - i1.y*i2.x > 0

/--
 True if the conjunction of i1 and i2 implies ninq
-/
def two_imply (i1 i2 : ineq) (ninq : ineq) : bool :=
(ninq.clockwise_of i1 && i2.clockwise_of ninq) || (i1.implies ninq) || (i2.implies ninq)

end ineq

section proof_objs

meta inductive diseq_proof : expr → expr → ℚ → Type
| hyp : Π lhs rhs c, expr → diseq_proof lhs rhs c
| sym : Π {lhs rhs c}, Π (dp : diseq_proof lhs rhs c), diseq_proof rhs lhs (1/c)

/-meta inductive ineq_proof : expr → expr → ineq → Type--(lhs rhs : expr) (r : comp) (c : ℚ)
| hyp : Π lhs rhs i, expr → ineq_proof lhs rhs i
| sym : Π {lhs rhs i}, ineq_proof lhs rhs i → ineq_proof rhs lhs (i.reverse)
| of_ineq_proof_and_diseq : Π {lhs rhs i c}, 
    ineq_proof lhs rhs i → diseq_proof lhs rhs c → ineq_proof lhs rhs (i.strengthen)
| of_ineq_proof_and_sign_lhs : Π {lhs rhs i c},
    ineq_proof lhs rhs i → sign_proof lhs c → ineq_proof lhs rhs (i.strengthen)

meta inductive sign_proof : expr → gen_comp → Type
| hyp  : Π e c, expr → sign_proof e c
| ineq_lhs : Π c, Π {lhs rhs iqp}, ineq_proof lhs rhs iqp → sign_proof lhs c
| ineq_rhs : Π c, Π {lhs rhs iqp}, ineq_proof lhs rhs iqp → sign_proof rhs c
| eq_of_two_eqs_lhs : Π {lhs rhs eqp1 eqp2}, 
    eq_proof lhs rhs eqp1 → eq_proof lhs rhs eqp2 → sign_proof lhs gen_comp.eq
| eq_of_two_eqs_rhs : Π {lhs rhs eqp1 eqp2}, 
    eq_proof lhs rhs eqp1 → eq_proof lhs rhs eqp2 → sign_proof rhs gen_comp.eq
| diseq_of_diseq_zero : Π {lhs rhs}, diseq_proof lhs rhs 0 → sign_proof lhs gen_comp.ne
| eq_of_eq_zero : Π {lhs rhs}, eq_proof lhs rhs 0 → sign_proof lhs gen_comp.eq-/


meta inductive eq_proof : expr → expr → ℚ → Type
| hyp : Π lhs rhs c, expr → eq_proof lhs rhs c
| sym : Π {lhs rhs c}, Π (ep : eq_proof lhs rhs c), eq_proof rhs lhs (1/c)

meta mutual inductive ineq_proof, sign_proof 
with ineq_proof : expr → expr → ineq → Type
| hyp : Π lhs rhs i, expr → ineq_proof lhs rhs i
| sym : Π {lhs rhs i}, ineq_proof lhs rhs i → ineq_proof rhs lhs (i.reverse)
| of_ineq_proof_and_diseq : Π {lhs rhs i c}, 
    ineq_proof lhs rhs i → diseq_proof lhs rhs c → ineq_proof lhs rhs (i.strengthen)
| of_ineq_proof_and_sign_lhs : Π {lhs rhs i c},
    ineq_proof lhs rhs i → sign_proof lhs c → ineq_proof lhs rhs (i.strengthen)
| of_ineq_proof_and_sign_rhs : Π {lhs rhs i c},
    ineq_proof lhs rhs i → sign_proof rhs c → ineq_proof lhs rhs (i.strengthen)
| zero_comp_of_sign_proof : Π {lhs c} rhs i, sign_proof lhs c → ineq_proof lhs rhs i

with sign_proof : expr → gen_comp → Type
| hyp  : Π e c, expr → sign_proof e c
| ineq_lhs : Π c, Π {lhs rhs iqp}, ineq_proof lhs rhs iqp → sign_proof lhs c
| ineq_rhs : Π c, Π {lhs rhs iqp}, ineq_proof lhs rhs iqp → sign_proof rhs c
| eq_of_two_eqs_lhs : Π {lhs rhs eqp1 eqp2}, 
    eq_proof lhs rhs eqp1 → eq_proof lhs rhs eqp2 → sign_proof lhs gen_comp.eq
| eq_of_two_eqs_rhs : Π {lhs rhs eqp1 eqp2}, 
    eq_proof lhs rhs eqp1 → eq_proof lhs rhs eqp2 → sign_proof rhs gen_comp.eq
| diseq_of_diseq_zero : Π {lhs rhs}, diseq_proof lhs rhs 0 → sign_proof lhs gen_comp.ne
| eq_of_eq_zero : Π {lhs rhs}, eq_proof lhs rhs 0 → sign_proof lhs gen_comp.eq
| ineq_of_eq_and_ineq_lhs : Π {lhs rhs i c}, Π c', 
    eq_proof lhs rhs c → ineq_proof lhs rhs i →  sign_proof lhs c'
| ineq_of_eq_and_ineq_rhs : Π {lhs rhs i c}, Π c', 
    eq_proof lhs rhs c → ineq_proof lhs rhs i →  sign_proof rhs c'
| ineq_of_ineq_and_eq_zero_rhs : Π {lhs rhs i}, Π c, 
    ineq_proof lhs rhs i → sign_proof lhs gen_comp.eq → sign_proof rhs c


open ineq_proof
meta def ineq_proof.to_format  {lhs rhs c} : ineq_proof lhs rhs c → format
| p := "proof"

meta instance (lhs rhs c) : has_to_format (ineq_proof lhs rhs c) :=
⟨ineq_proof.to_format⟩

end proof_objs

section data_objs

meta structure ineq_data (lhs rhs : expr) :=
(inq : ineq)
(prf : ineq_proof lhs rhs inq)

meta def ineq_data.reverse {lhs rhs : expr} (id : ineq_data lhs rhs) : ineq_data rhs lhs :=
⟨id.inq.reverse, id.prf.sym⟩

meta def ineq_data.to_format {lhs rhs} : ineq_data lhs rhs → format
| ⟨inq, prf⟩ := "⟨" ++ to_fmt inq ++ " : " ++ to_fmt prf ++ "⟩"

meta instance ineq_data.has_to_format (lhs rhs) : has_to_format (ineq_data lhs rhs) :=
⟨ineq_data.to_format⟩

meta structure eq_data (lhs rhs : expr) :=
(c   : ℚ)
(prf : eq_proof lhs rhs c)

meta def eq_data.reverse {lhs rhs : expr} (ei : eq_data lhs rhs) : eq_data rhs lhs :=
⟨(1/ei.c), ei.prf.sym⟩

meta def eq_data.implies_ineq {lhs rhs} (ed : eq_data lhs rhs) (id : ineq) : bool :=
match id.to_slope with
| slope.some c := c = ed.c ∧ bnot (id.strict)
| horiz        := ff
end

meta def eq_data.to_format {lhs rhs} : eq_data lhs rhs → format
| ⟨c, prf⟩ := "⟨(lhs)=" ++ to_fmt c ++ "*(rhs)⟩" 

meta instance eq_data.has_to_format (lhs rhs) : has_to_format (eq_data lhs rhs) :=
⟨eq_data.to_format⟩

meta structure diseq_data (lhs rhs : expr) :=
(c : ℚ)
(prf : diseq_proof lhs rhs c)

meta def diseq_data.reverse {lhs rhs : expr} (di : diseq_data lhs rhs) : diseq_data rhs lhs :=
⟨(1/di.c), di.prf.sym⟩

meta structure sign_data (e : expr) :=
(c : gen_comp)
(prf : sign_proof e c)


end data_objs


section info_objs

/--
 In the two_comps case, we maintain the invariant that the defining ray of the first is 
 counterclockwise to that of the second.
-/
meta inductive ineq_info (lhs rhs : expr)
| no_comps {}  : ineq_info
| one_comp     : ineq_data lhs rhs → ineq_info
| two_comps    : ineq_data lhs rhs → ineq_data lhs rhs → ineq_info
| equal        : eq_data lhs rhs → ineq_info
open ineq_info


meta def ineq_info.mk_two_comps {lhs rhs} (id1 id2 : ineq_data lhs rhs) : ineq_info lhs rhs :=
if id2.inq.clockwise_of id1.inq then two_comps id1 id2 else two_comps id2 id1

meta instance ineq_info.inhabited (lhs rhs) : inhabited (ineq_info lhs rhs) :=
⟨no_comps⟩

meta def ineq_info.reverse {lhs rhs : expr} : ineq_info lhs rhs → ineq_info rhs lhs
| no_comps            := no_comps
| (one_comp id1)      := one_comp id1.reverse
| (two_comps id1 id2) := two_comps id1.reverse id2.reverse
| (equal ed)          := equal ed.reverse

meta def ineq_info.to_format {lhs rhs} : ineq_info lhs rhs → format
| no_comps := "ineq_info.empty"
| (one_comp id1) := "{" ++ to_fmt id1 ++ "}"
| (two_comps id1 id2) := "{" ++ to_fmt id1 ++ " | " ++ to_fmt id2 ++ "}"
| (equal ed) := "{" ++ to_fmt ed ++ "}"

meta instance ineq_info.has_to_format (lhs rhs) : has_to_format (ineq_info lhs rhs) :=
⟨ineq_info.to_format⟩

/-meta def eq_info (lhs rhs : expr) := option (eq_data lhs rhs)

meta instance eq_info.inhabited (lhs rhs) : inhabited (eq_info lhs rhs) :=
⟨none⟩


meta def eq_info.reverse {lhs rhs : expr} : eq_info lhs rhs → eq_info rhs lhs
| none      := none
| (some ei) := some (ei.reverse)
-/

meta def diseq_info (lhs rhs : expr) := rb_map ℚ (diseq_data lhs rhs)

meta instance diseq_info.inhabited (lhs rhs) : inhabited (diseq_info lhs rhs) :=
⟨mk_rb_map⟩

meta def diseq_info.reverse {lhs rhs : expr} : diseq_info lhs rhs → diseq_info rhs lhs :=
rb_map.map diseq_data.reverse


meta def sign_info (e : expr) := option (sign_data e)

meta def sign_info.is_strict {e : expr} : sign_info e → bool
| (some sd) := sd.c.is_strict
| none := ff

meta instance sign_info.inhabited (lhs) : inhabited (sign_info lhs) :=
⟨none⟩

end info_objs

open ineq_proof eq_proof diseq_proof sign_proof ineq_info diseq_info sign_info

meta def point_of_coeff_and_comps (c : ℚ) : option gen_comp → option gen_comp → option (ℚ × ℚ)
| (some gen_comp.eq) r := point_of_coeff_and_comps none r
| (some gen_comp.ne) r := point_of_coeff_and_comps none r
| l (some gen_comp.eq) := point_of_coeff_and_comps l none
| l (some gen_comp.ne) := point_of_coeff_and_comps l none
| (some l) none := if l.is_less then some (-1, -1/c) else some (1, 1/c)
| none (some r) := if r.is_less then some (-c, -1) else some (c, 1)
| none none := none
| (some l) (some r) := 
if (c ≥ 0) && (l.is_less = r.is_less) then point_of_coeff_and_comps (some l) none
else if (c < 0) && bnot (l.is_less = r.is_less) then point_of_coeff_and_comps (some l) none
else none

private meta def comp_option_of_sign_info {e} : sign_info e → option gen_comp
| (some c) := c.c
| none := none

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
  let pr1 := sign_proof.eq_of_eq_zero (by rw -h; apply ed.prf),
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
let cmp  := if m - ed.c > 0 then id.to_comp else id.to_comp.reverse in 
if ed.c > 0 then 
  let pr1 := sign_proof.ineq_of_eq_and_ineq_lhs cmp ed.prf prf,
      pr2 := sign_proof.ineq_of_eq_and_ineq_rhs cmp ed.prf prf in
      (some ⟨_, pr1⟩, some ⟨_, pr2⟩)
else if h : ed.c = 0 then
  let pr1 := sign_proof.eq_of_eq_zero (by rw -h; apply ed.prf),
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
match point_of_coeff_and_comps ed.c (comp_option_of_sign_info sil) (comp_option_of_sign_info sir) with
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

section two_var_ineqs

meta def ineq_info.implies_ineq {lhs rhs : expr} : ineq_info lhs rhs → ineq → bool
| (one_comp ⟨inq1, _⟩) ninq := inq1.implies ninq
| (two_comps ⟨inq1, _⟩ ⟨inq2, _⟩) ninq := ineq.two_imply inq1 inq2 ninq
| (equal ed) ninq := ed.implies_ineq ninq
| _ _ := ff

meta def ineq_info.implies {lhs rhs : expr} (ii : ineq_info lhs rhs) (id : ineq_data lhs rhs) : bool :=
ii.implies_ineq id.inq

end two_var_ineqs

meta inductive contrad
| none : contrad
| eq_diseq : Π {lhs rhs}, eq_data lhs rhs → diseq_data lhs rhs → contrad
| ineqs : Π {lhs rhs}, ineq_info lhs rhs → ineq_data lhs rhs → contrad
| sign : Π {e}, sign_data e → sign_data e → contrad
| strict_ineq_self : Π {e}, ineq_data e e → contrad

end polya
