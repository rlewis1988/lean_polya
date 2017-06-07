import data.hash_map .rat_additions

   
meta def reduce_option_list {α} : list (option α) → list α
| [] := []
| (none::l) := reduce_option_list l
| (some a::l) := a::reduce_option_list l

meta def rb_set.insert_list {α : Type} (s : rb_set α) (l : list α) : rb_set α :=
l.foldr (λ a s', s'.insert a) s

instance : has_ordering ℚ :=
⟨λ a b, if a = b then ordering.eq else if a < b then ordering.lt else ordering.gt⟩

namespace hash_map
def {u v} find' {α : Type u} {β : α → Type v} [decidable_eq α] (m : hash_map α β) (a : α) [inhabited (β a)] : β a :=
match m.find a with
| none := default _
| some b := b
end
end hash_map

meta def string.to_name (s : string) : name :=
name.mk_string s name.anonymous

meta def rb_set.of_list {α} [has_ordering α] (l : list α) : rb_set α :=
l.foldl (λ s a, s.insert a) mk_rb_set

meta def rb_set.union {α} (s1 s2 : rb_set α) : rb_set α :=
s1.fold s2 (λ s c, c.insert s)

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

meta def to_pexpr : comp → pexpr
| le := ``(has_le.le)
| lt := ``(has_lt.lt)
| ge := ``(ge)
| gt := ``(gt)

section
open tactic
meta def to_function (lhs rhs : expr) : comp → tactic expr
| lt := to_expr ``(%%lhs < %%rhs)
| le := to_expr ``(%%lhs ≤ %%rhs)
| gt := to_expr ``(%%lhs > %%rhs)
| ge := to_expr ``(%%lhs ≥ %%rhs)
end

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
| eq := eq
| ne := ne

def negate : gen_comp → gen_comp
| le := gt
| lt := ge
| ge := lt
| gt := le
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

def strongest : gen_comp → gen_comp → gen_comp
| gt ge := gt
| lt le := lt
| ge gt := gt
| le lt := lt
| eq b  := b
| a eq  := a
| a b   := if a = b then a else b

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

/--
 Be careful. In the ne or eq case, this returns ge.
-/
meta def to_comp : gen_comp → comp
| le := comp.le
| lt := comp.lt
| ge := comp.ge
| gt := comp.gt
| _  := comp.ge

meta instance : has_to_format gen_comp :=
⟨to_format⟩

end gen_comp

inductive spec_comp
| lt | le | eq

def spec_comp_and_flipped_of_comp : comp → spec_comp × bool
| comp.lt := (spec_comp.lt, ff)
| comp.le := (spec_comp.le, ff)
| comp.gt := (spec_comp.lt, tt)
| comp.ge := (spec_comp.le, tt)

namespace spec_comp

instance : decidable_eq spec_comp := by tactic.mk_dec_eq_instance

def strongest : spec_comp → spec_comp → spec_comp
| spec_comp.lt _ := spec_comp.lt
| _ spec_comp.lt := spec_comp.lt
| spec_comp.le _ := spec_comp.le
| _ spec_comp.le := spec_comp.le
| spec_comp.eq spec_comp.eq := spec_comp.eq

/--
 This is nonsense on eq
-/
def to_comp : spec_comp → comp
| spec_comp.lt := comp.lt
| spec_comp.le := comp.le
| spec_comp.eq := comp.gt

meta def to_format : spec_comp → format
| spec_comp.lt := "<"
| spec_comp.le := "≤"
| spec_comp.eq := "="

meta instance has_to_format : has_to_format spec_comp :=
⟨spec_comp.to_format⟩

end spec_comp

/--
 This does not represent the traditional slope, but (x/y) if (x, y) is a point on the line
-/
inductive slope
| horiz : slope
| some : rat → slope

instance slope.decidable_eq : decidable_eq slope := by tactic.mk_dec_eq_instance

meta def slope.to_format : slope → format
| slope.horiz := "horiz"
| (slope.some m) := to_fmt m

meta instance : has_to_format slope :=
⟨slope.to_format⟩ 

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

def is_axis (i : ineq) : bool :=
(i.x = 0) || (i.y = 0)

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

meta def is_zero_slope (i : ineq) : bool :=
(i.x = 0) && bnot (i.y = 0)

meta def is_horiz (i : ineq) : bool :=
i.y = 0

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

@[reducible]
meta def sum_form := rb_map expr ℚ

namespace sum_form

meta def zero : sum_form := rb_map.mk _ _
meta instance : has_zero sum_form := ⟨sum_form.zero⟩

meta def of_expr (e : expr) : sum_form := 
mk_rb_map.insert e 1

meta def get_coeff (sf : sum_form) (e : expr) : ℚ :=
match sf.find e with
| some q := q
| none := 0
end

meta def get_nonzero_factors (sf : sum_form) : list (expr × ℚ) :=
sf.to_list

meta def add_coeff (sf : sum_form) (e : expr) (c : ℚ) : sum_form :=
if (sf.get_coeff e) + c = 0 then sf.erase e
else sf.insert e ((sf.get_coeff e) + c)

meta def add (lhs rhs : sum_form) : sum_form :=
rhs.fold lhs (λ e q sf, sf.add_coeff e q)

meta def scale (sf : sum_form) (c : ℚ) : sum_form :=
sf.map (λ q, if q=1/c then 1 else c*q) -- replace this with a real implementation of ℚ

meta def sub (lhs rhs : sum_form) : sum_form :=
lhs.add (rhs.scale (-1))

meta def negate (lhs : sum_form) : sum_form :=
lhs.scale (-1)

meta instance : has_add sum_form := ⟨sum_form.add⟩
meta instance : has_sub sum_form := ⟨sum_form.sub⟩

meta def add_factor (lhs rhs : sum_form) (c : ℚ) : sum_form :=
lhs + (rhs.scale c)

meta def normalize (sf : sum_form) : sum_form :=
match rb_map.to_list sf with
| [] := sf
| (_, m)::t := if abs m = 1 then sf else sf.scale (abs (1/m))
end

meta def is_normalized (sd : sum_form) : bool :=
match rb_map.to_list sd with
| [] := tt
| (_, m)::t := abs m = 1
end


end sum_form

meta structure sum_form_comp :=
(sf : sum_form) (c : spec_comp) 

namespace sum_form_comp


meta instance sum_form_comp.has_to_format : has_to_format sum_form_comp :=
⟨λ sfc, "{" ++ to_fmt (sfc.sf) ++ to_fmt sfc.c ++ "0}"⟩

/--
 This is only valid for positive m
-/
meta def scale (m : ℚ) : sum_form_comp → sum_form_comp
| ⟨sf, c⟩ := ⟨sf.scale m, c⟩


meta def normalize : sum_form_comp → sum_form_comp
| ⟨sf, c⟩ := ⟨sf.normalize, c⟩

meta def is_normalized : sum_form_comp → bool
| ⟨sf, _⟩ := sf.is_normalized

meta def is_contr : sum_form_comp → bool
| ⟨sf, c⟩ := (c = spec_comp.lt) && (sf.keys.length = 0)


meta def of_ineq (lhs rhs : expr) (id : ineq) : sum_form_comp :=
match id.to_slope, spec_comp_and_flipped_of_comp id.to_comp with
| slope.horiz, (cmp, flp) := ⟨if flp then (sum_form.of_expr rhs).negate else sum_form.of_expr rhs, cmp⟩
| slope.some m, (cmp, flp) := 
   let nsfc := (sum_form.of_expr lhs).add_factor (sum_form.of_expr rhs) (-m) in
   ⟨if flp then nsfc.negate else nsfc, cmp⟩
end

meta def of_eq (lhs rhs : expr) (c : ℚ) : sum_form_comp :=
⟨(sum_form.of_expr lhs).add_factor (sum_form.of_expr rhs) (-c), spec_comp.eq⟩

meta def of_sign (e : expr) : gen_comp → sum_form_comp
| gen_comp.ne := ⟨mk_rb_map, spec_comp.eq⟩
| gen_comp.eq := ⟨sum_form.of_expr e, spec_comp.eq⟩
| gen_comp.le := ⟨sum_form.of_expr e, spec_comp.le⟩
| gen_comp.lt := ⟨sum_form.of_expr e, spec_comp.lt⟩
| gen_comp.ge := ⟨(sum_form.of_expr e).scale (-1), spec_comp.le⟩
| gen_comp.gt := ⟨(sum_form.of_expr e).scale (-1), spec_comp.lt⟩


--(sum_form_comp.of_eq lhs rhs c

end sum_form_comp


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


/-meta inductive eq_proof : expr → expr → ℚ → Type
| hyp : Π lhs rhs c, expr → eq_proof lhs rhs c
| sym : Π {lhs rhs c}, Π (ep : eq_proof lhs rhs c), eq_proof rhs lhs (1/c)-/

meta mutual inductive eq_proof, ineq_proof, sign_proof, sum_form_proof
with eq_proof : expr → expr → ℚ → Type
| hyp : Π lhs rhs c, expr → eq_proof lhs rhs c
| sym : Π {lhs rhs c}, Π (ep : eq_proof lhs rhs c), eq_proof rhs lhs (1/c)
| of_opp_ineqs : Π {lhs rhs i}, Π c,
  ineq_proof lhs rhs i → ineq_proof lhs rhs (i.reverse) → eq_proof lhs rhs c
| of_sum_form_proof : Π lhs rhs c {sf}, sum_form_proof ⟨sf, spec_comp.eq⟩ → eq_proof lhs rhs c
| adhoc : Π lhs rhs c, tactic expr → eq_proof lhs rhs c

with ineq_proof : expr → expr → ineq → Type
| hyp : Π lhs rhs i, expr → ineq_proof lhs rhs i
| sym : Π {lhs rhs i}, ineq_proof lhs rhs i → ineq_proof rhs lhs (i.reverse)
| of_ineq_proof_and_diseq : Π {lhs rhs i c}, 
    ineq_proof lhs rhs i → diseq_proof lhs rhs c → ineq_proof lhs rhs (i.strengthen)
| of_ineq_proof_and_sign_lhs : Π {lhs rhs i c},
    ineq_proof lhs rhs i → sign_proof lhs c → ineq_proof lhs rhs (i.strengthen)
| of_ineq_proof_and_sign_rhs : Π {lhs rhs i c},
    ineq_proof lhs rhs i → sign_proof rhs c → ineq_proof lhs rhs (i.strengthen)
| zero_comp_of_sign_proof : Π {lhs c} rhs i, sign_proof lhs c → ineq_proof lhs rhs i| of_sum_form_proof : Π lhs rhs i {sfc}, sum_form_proof sfc → ineq_proof lhs rhs i
| adhoc : Π lhs rhs i, tactic expr → ineq_proof lhs rhs i

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
| of_sum_form_proof : Π e c {sfc}, sum_form_proof sfc → sign_proof e c
| adhoc : Π e c, tactic expr → sign_proof e c

with sum_form_proof : sum_form_comp → Type
| of_ineq_proof : Π {lhs rhs iq}, Π id : ineq_proof lhs rhs iq,
    sum_form_proof (sum_form_comp.of_ineq lhs rhs iq)
| of_eq_proof : Π {lhs rhs c}, Π id : eq_proof lhs rhs c,
    sum_form_proof (sum_form_comp.of_eq lhs rhs c)
| of_sign_proof : Π {e c}, Π id : sign_proof e c, sum_form_proof (sum_form_comp.of_sign e c)
| of_add_factor_same_comp : Π {lhs rhs c1 c2}, Π m : ℚ, -- assumes m is positive
  sum_form_proof ⟨lhs, c1⟩ → sum_form_proof ⟨rhs, c2⟩ → sum_form_proof ⟨lhs.add_factor rhs m, spec_comp.strongest c1 c2⟩ 
| of_add_eq_factor_op_comp : Π {lhs rhs c1}, Π m : ℚ, -- assumes m is negative
  sum_form_proof ⟨lhs, c1⟩ → sum_form_proof ⟨rhs, spec_comp.eq⟩ → sum_form_proof ⟨lhs.add_factor rhs m, c1⟩ 
| of_scale : Π {sfc}, Π m, sum_form_proof sfc → sum_form_proof (sfc.scale m)
| of_expr_def : Π (e : expr) (sf : sum_form),  sum_form_proof ⟨sf, spec_comp.eq⟩ 
| fake : Π sd, sum_form_proof sd


open ineq_proof
meta def ineq_proof.to_format  {lhs rhs c} : ineq_proof lhs rhs c → format
| p := "proof"

meta def ineq_proof.to_format2 :
     Π {lhs rhs : expr} {iq : ineq}, ineq_proof lhs rhs iq → format
| .(_) .(_) .(_) (hyp (lhs) (rhs) (iq) e) := "hyp"
| .(_) .(_) .(_) (@sym lhs rhs c ip) := "sym"
| .(_) .(_) .(_) (@of_ineq_proof_and_diseq lhs rhs iq c ip dp) := "of_ineq_proof_and_diseq"
| .(_) .(_) .(_) (@of_ineq_proof_and_sign_lhs lhs rhs iq c ip sp) := "of_ineq_proof_and_sign_lhs"
| .(_) .(_) .(_) (@of_ineq_proof_and_sign_rhs lhs rhs iq c ip sp) :=  "of_ineq_proof_and_sign_rhs"
| .(_) .(_) .(_) (@zero_comp_of_sign_proof lhs c rhs iq sp) := "zero_comp_of_sign"
| .(_) .(_) .(_) (@of_sum_form_proof lhs rhs i _ sp) := "of_sum_form"
| .(_) .(_) .(_) (adhoc _ _ _ t) := "adhoc"

meta instance ineq_proof.has_to_format (lhs rhs c) : has_to_format (ineq_proof lhs rhs c) :=
⟨ineq_proof.to_format2⟩

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

-- TODO
section
open tactic


-- TODO : add proof argument and move
meta def ineq.to_type (id : ineq) (lhs rhs : expr) : tactic expr :=
match id.to_slope with
| slope.horiz := id.to_comp.to_function rhs `(0 : ℚ) --, to_expr `(fake_ineq_to_expr_proof %%tp)
| slope.some m := 
 -- let rhs' : expr := (if m=0 then `(0 : ℚ) else `(m*%%rhs : ℚ)) in
do rhs' ← to_expr (if m=0 then ``(0 : ℚ) else ``(%%(↑(reflect m) : expr)*%%rhs : ℚ)),
     id.to_comp.to_function lhs rhs'
     --to_expr `(fake_ineq_to_expr_proof %%tp)
end 

end 

/- meta def ineq_data.to_expr {lhs rhs} (id : ineq_data lhs rhs) : tactic expr :=
id.inq.to_expr lhs rhs -/

meta structure eq_data (lhs rhs : expr) :=
(c   : ℚ)
(prf : eq_proof lhs rhs c)

meta def eq_data.reverse {lhs rhs : expr} (ei : eq_data lhs rhs) : eq_data rhs lhs :=
⟨(1/ei.c), ei.prf.sym⟩

meta def eq_data.implies_ineq {lhs rhs} (ed : eq_data lhs rhs) (id : ineq) : bool :=
match id.to_slope with
| slope.some c := (c = ed.c) && bnot (id.strict)
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

meta def sign_data.to_format {e} : sign_data e → format
| ⟨c, _⟩ := to_fmt "{" ++ to_fmt e ++ to_fmt c ++ to_fmt "0}"

meta instance sign_data.has_to_format {e} : has_to_format (sign_data e) :=
⟨sign_data.to_format⟩ 

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

@[reducible]
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
let cmp  := if m - ed.c < 0 then id.to_comp else id.to_comp.reverse in 
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

namespace sum_form_comp

-- is this needed?
meta def of_ineq_proof {lhs rhs id} (ip : ineq_proof lhs rhs id) : sum_form_comp :=
sum_form_comp.of_ineq lhs rhs id

end sum_form_comp  

meta structure sum_form_comp_data :=
(sfc : sum_form_comp) (prf : sum_form_proof sfc) (elim_list : rb_set expr)

namespace sum_form_comp_data

meta def of_ineq_data {lhs rhs} (id : ineq_data lhs rhs) : sum_form_comp_data :=
⟨_, sum_form_proof.of_ineq_proof id.prf, mk_rb_set⟩

meta def of_eq_data {lhs rhs} (ed : eq_data lhs rhs) : sum_form_comp_data :=
⟨_, sum_form_proof.of_eq_proof ed.prf, mk_rb_set⟩

meta def of_sign_data {e} (sd : sign_data e) : sum_form_comp_data :=
⟨_, sum_form_proof.of_sign_proof sd.prf, mk_rb_set⟩

meta def vars (sfcd : sum_form_comp_data) : list expr :=
sfcd.sfc.sf.keys


  

meta instance : has_to_format sum_form_comp_data :=
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

-- TODO: do we need to take elim_vars into account for this order?
meta def sum_form_comp_data.order : sum_form_comp_data → sum_form_comp_data → ordering
| ⟨sfc1, _, _⟩ ⟨sfc2, _, _⟩ := sfc1.order sfc2

meta instance sum_form.has_ordering : has_ordering sum_form :=
⟨sum_form.order⟩

meta instance sum_form_comp_data.has_ordering : has_ordering sum_form_comp_data := 
⟨sum_form_comp_data.order⟩

meta inductive contrad
| none : contrad
| eq_diseq : Π {lhs rhs}, eq_data lhs rhs → diseq_data lhs rhs → contrad
| ineqs : Π {lhs rhs}, ineq_info lhs rhs → ineq_data lhs rhs → contrad
| sign : Π {e}, sign_data e → sign_data e → contrad
| strict_ineq_self : Π {e}, ineq_data e e → contrad
| sum_form : Π {sfc}, sum_form_proof sfc → contrad

meta def contrad.to_format : contrad → format
| contrad.none := "no contradiction"
| (@contrad.eq_diseq lhs rhs _ _) := "eq_diseq"
| (@contrad.ineqs lhs rhs _ _) := "ineqs"
| (@contrad.sign e _ _) := "sign"
| (@contrad.strict_ineq_self e _) := "strict_ineq_self"
| (@contrad.sum_form _ sfcd) := "sum_form"

meta instance contrad.has_to_format : has_to_format contrad :=
⟨contrad.to_format⟩

end polya
