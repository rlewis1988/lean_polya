import data.hash_map .rat_additions

def {u} list.bfilter {α : Type u} (p : α → bool) : list α → list α
| [] := []
| (h::t) := if p h then h::list.bfilter t else list.bfilter t

def {u v} list.mfoldl' {m : Type u → Type v} [monad m] {s : Type u} : (s → s → m s) → s → list s → m s
| f s [] := return s
| f s [a] := return a
| f s (h :: r) := do
  s' ← f s h,
  list.mfoldl f s' r


local infix `^` := rat.pow
   
meta def reduce_option_list {α} : list (option α) → list α
| [] := []
| (none::l) := reduce_option_list l
| (some a::l) := a::reduce_option_list l

namespace hash_map
def {u v} find' {α : Type u} {β : α → Type v} [decidable_eq α] (m : hash_map α β) (a : α) [inhabited (β a)] : β a :=
match m.find a with
| none := default _
| some b := b
end
end hash_map

meta def string.to_name (s : string) : name :=
name.mk_string s name.anonymous

namespace polya

@[derive decidable_eq]
inductive comp
| le | lt | ge | gt

@[derive decidable_eq]
inductive gen_comp
| le | lt | ge | gt | eq | ne

@[derive decidable_eq]
inductive spec_comp
| lt | le | eq

namespace comp
--instance : decidable_eq comp := by tactic.mk_dec_eq_instance

def dir : comp → ℤ
| le := -1
| lt := -1
| ge := 1
| gt := 1

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

def is_greater : comp → bool := bnot ∘ is_less

def implies (c1 c2 : comp) : bool :=
(is_less c1 = is_less c2) && (is_strict c1 || bnot (is_strict c2))

meta def to_format : comp → format
| le := "≤"
| lt := "<"
| ge := "≥"
| gt := ">"

def to_gen_comp : comp → gen_comp
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

def prod : comp → comp → comp
| gt a := a
| a gt := a
| ge ge := ge
| ge lt := le
| ge le := le
| lt ge := le
| le ge := le
| le le := ge
| le lt := ge
| lt le := ge
| lt lt := gt

meta instance : has_coe comp gen_comp :=
⟨to_gen_comp⟩ 

meta instance : has_to_format comp :=
⟨to_format⟩

end comp

namespace gen_comp
--instance : decidable_eq gen_comp := by tactic.mk_dec_eq_instance
instance : inhabited gen_comp := ⟨eq⟩

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

def is_greater : gen_comp → bool
| gt := tt
| ge := tt
| _ := ff

def is_less_or_eq : gen_comp → bool
| lt := tt
| le := tt
| eq := tt
| _ := ff

def is_greater_or_eq : gen_comp → bool
| gt := tt
| ge := tt
| eq := tt
| _ := ff

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

def contr : gen_comp → gen_comp → bool
| lt gt := tt
| lt ge := tt
| lt eq := tt
| le gt := tt
| eq ne := tt
| eq lt := tt
| eq gt := tt
| ge lt := tt
| gt lt := tt
| gt le := tt
| gt eq := tt
| _ _ := ff

def prod : gen_comp → gen_comp → option gen_comp
| ne ne := ne
| ne eq := eq
| eq ne := eq
| ne gt := ne
| ne lt := ne
| gt ne := ne
| lt ne := ne
| ne a := none
| a ne := none
| gt a := a
| a gt := a
| eq a := eq
| a eq := eq
| ge ge := ge
| ge le := le
| le ge := le
| ge lt := le
| lt ge := le
| le le := ge
| le lt := ge
| lt le := ge
| lt lt := gt

-- may not be right for = or ≠
def pow (c1 : gen_comp) (z : ℤ) : gen_comp :=
if (bnot c1.is_less) || (z ≥ 0) || (z % 2 = 0) then c1 
else c1.reverse

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

/--
 Be careful. This only matches strength
-/
meta def to_spec_comp : gen_comp → spec_comp
| le := spec_comp.le
| ge := spec_comp.le
| lt := spec_comp.lt
| gt := spec_comp.lt
| _ := spec_comp.eq

meta def to_function (lhs rhs : expr) : gen_comp → tactic expr
| le := tactic.to_expr ``(%%lhs ≤ %%rhs)
| lt := tactic.to_expr ``(%%lhs < %%rhs)
| ge := tactic.to_expr ``(%%lhs ≥ %%rhs)
| gt := tactic.to_expr ``(%%lhs > %%rhs)
| eq := tactic.to_expr ``(%%lhs = %%rhs)
| ne := tactic.to_expr ``(%%lhs ≠ %%rhs)

meta instance : has_to_format gen_comp :=
⟨to_format⟩


end gen_comp


def spec_comp_and_flipped_of_comp : comp → spec_comp × bool
| comp.lt := (spec_comp.lt, ff)
| comp.le := (spec_comp.le, ff)
| comp.gt := (spec_comp.lt, tt)
| comp.ge := (spec_comp.le, tt)

namespace spec_comp

--instance : decidable_eq spec_comp := by tactic.mk_dec_eq_instance

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

def to_gen_comp : spec_comp → gen_comp
| spec_comp.lt := gen_comp.lt
| spec_comp.le := gen_comp.le
| spec_comp.eq := gen_comp.eq

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
@[derive decidable_eq]
inductive slope
| horiz : slope
| some : rat → slope

--instance slope.decidable_eq : decidable_eq slope := by tactic.mk_dec_eq_instance

meta def slope.to_format : slope → format
| slope.horiz := "horiz"
| (slope.some m) := to_fmt m

meta instance : has_to_format slope :=
⟨slope.to_format⟩ 

meta def slope.invert : slope → slope
| slope.horiz := slope.some 0
| (slope.some m) := if m = 0 then slope.horiz else slope.some (1/m)

/--
 An inequality (str, a, b) represents the halfplane counterclockwise from the vector (a, b).
 If str is true, it is strict (ie, it doesn't include the line bx-ay=0).
-/
@[derive decidable_eq]
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

open polya.comp slope

def to_comp (i : ineq) : comp := -- DOUBLE CHECK THIS
/-if i.x ≥ 0 then
  if i.y > 0 then
    if i.strict then lt else le
  else 
    if i.strict then gt else ge
else
  if i.y > 0 then
    if i.strict then lt else le
  else
    if i.strict then gt else ge-/
if i.y > 0 then
  if i.strict then lt else le
else if i.y < 0 then
  if i.strict then gt else ge
else if i.x < 0 then
  if i.strict then lt else le
else if i.strict then gt else ge

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

section proof_sketch

meta inductive proof_sketch
| mk (fact : string) (reason : string) (justifications : list proof_sketch) : proof_sketch

meta def proof_sketch.justifications : proof_sketch → list proof_sketch
| ⟨_, _, j⟩ := j

meta def proof_sketch.reason : proof_sketch → string
| ⟨_, r, _⟩ := r


end proof_sketch

open native

@[reducible]
meta def sum_form := rb_map expr ℚ

meta def expr_coeff_list_to_expr : list (expr × ℚ) → tactic expr
| [] := return `(0 : ℚ)
| [(e, q)] := tactic.to_expr ``(%%(↑q.reflect : expr)*%%e)
| ((e, q)::t) := do e' ← expr_coeff_list_to_expr t, h ← tactic.to_expr ``(%%(q.reflect : expr)*%%e), tactic.to_expr ``(%%h + %%e')

meta def sum_form.to_expr (sf : sum_form) : tactic expr := 
expr_coeff_list_to_expr sf.to_list

namespace sum_form

meta def to_tactic_format (sf : sum_form) : tactic format :=
do exs ← sf.to_list.mmap (λ pr, do e ← to_string <$> tactic.pp pr.1, return $ e ++ " ← " ++ repr pr.2 ++ ", "),
   return $ "{ " ++ string.join exs ++ " }" 

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

meta def sum_form_comp.to_expr (sfc : sum_form_comp) : tactic expr :=
do e ← sfc.sf.to_expr,
   sfc.c.to_comp.to_function e `(0 : ℚ)


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

meta structure prod_form := 
(coeff : ℚ)
(exps : rb_map expr ℤ)

namespace prod_form
protected meta def one : prod_form := ⟨1, mk_rb_map⟩

meta instance : has_one prod_form := ⟨prod_form.one⟩

meta def get_exp (pf : prod_form) (e : expr) := 
match pf.exps.find e with
| some z := z
| none := 0
end

-- this assumes e ≠ 0
meta def mul_exp (pf : prod_form) (e : expr) (c : ℤ) : prod_form :=
if pf.get_exp e + c = 0 then {pf with exps := pf.exps.erase e}
else {pf with exps := pf.exps.insert e ((pf.get_exp e) + c)}

protected meta def mul (lhs rhs : prod_form) : prod_form :=
{rhs.exps.fold lhs (λ e q pf, pf.mul_exp e q) with coeff := lhs.coeff * rhs.coeff}

meta def scale (pf : prod_form) (q : ℚ) : prod_form :=
{pf with coeff := pf.coeff * q}

meta def pow (pf : prod_form) (z : ℤ) : prod_form :=
{coeff := if pf.coeff = 1 then pf.coeff else if z = 1 then pf.coeff else pf.coeff^z, exps := pf.exps.map (λ q, q*z)}


meta instance : has_mul prod_form := ⟨prod_form.mul⟩ 

meta def of_expr (e : expr) : prod_form :=
{coeff := 1, exps := mk_rb_map.insert e 1}

meta def get_nonone_factors (pf : prod_form) : list (expr × ℤ) :=
pf.exps.to_list

meta instance : has_to_format prod_form :=
⟨λ pf, to_fmt pf.coeff ++ "*" ++ to_fmt pf.exps⟩

end prod_form

-- 1 c pf
meta structure prod_form_comp :=
(pf : prod_form) (c : spec_comp)

namespace prod_form_comp

meta def default : prod_form_comp := ⟨prod_form.one, spec_comp.eq⟩

meta instance has_to_format : has_to_format prod_form_comp :=
⟨λ sfc, "{1" ++ to_fmt sfc.c ++ to_fmt sfc.pf.coeff ++ "*" ++ to_fmt (sfc.pf.exps) ++  "}"⟩

meta def is_contr : prod_form_comp → bool
| ⟨sf, c⟩ := (sf.exps.keys.length = 0) &&
    (((c = spec_comp.lt) && (sf.coeff ≥ 0)) || ((c = spec_comp.le) && (sf.coeff > 0)))




/-
-- assumes that lhs is positive
meta def of_ineq_pos_lhs (lhs rhs : expr) (id : ineq) : prod_form_comp :=
match id.to_slope, spec_comp_and_flipped_of_comp id.to_comp with
| slope.horiz, (cmp, flp) := default
| slope.some m, (cmp, flp) := 
   if m = 0 then default else
   let nsfc := ((prod_form.of_expr lhs).pow (-1)) * (prod_form.of_expr rhs) in
   ⟨if flp then (nsfc.scale m).pow (-1) else nsfc.scale m, cmp⟩
end

-- assumes that lhs is negative
meta def of_ineq_neg_lhs (lhs rhs : expr) (id : ineq) : prod_form_comp :=
match id.to_slope, spec_comp_and_flipped_of_comp id.to_comp with
| slope.horiz, (cmp, flp) := default
| slope.some m, (cmp, flp) := 
   if m = 0 then default else
   let nsfc := ((prod_form.of_expr lhs).pow (-1)) * (prod_form.of_expr rhs) in
   ⟨if flp then nsfc.scale m else (nsfc.scale m).pow (-1), cmp⟩--⟨nsfc.scale (if flp then m else -m), cmp⟩
end
-/

-- is_redundant_data cmp is_pos_coeff s_lhs s_rhs assumes lhs has sign s_lhs, rhs has sign s_rhs, c has sign is_pos_coeff,
-- and returns true if lhs cmp 0 cmp c*rhs
private meta def is_redundant_data (cmp : comp) (is_pos_coeff : bool) (s_lhs s_rhs : gen_comp) : bool :=
if s_lhs.is_less = s_rhs.is_less then 
   if is_pos_coeff then ff else cmp.is_less
else if s_lhs.is_less then 
   if is_pos_coeff then cmp.is_less else ff
else 
   if is_pos_coeff then bnot cmp.is_less else ff 


-- lhs cl 0 and rhs cr 0, and iq lhs rhs. cl and cr should be strict ineqs
meta def of_ineq (lhs rhs : expr) (cl cr : gen_comp) (iq : ineq) : prod_form_comp :=
match (/-trace_val-/ ("iq slope, lhs, rhs:", iq.to_slope, lhs, rhs)).2.1, (/-trace_val-/ ("iq comp:", iq.to_comp)).2 with
| slope.horiz, _ := default
| slope.some m, cmp := 
   if (m = 0) || (is_redundant_data cmp (m > 0) cl cr) then (/-trace_val-/ ("redundant", default)).2 else
   let nsfc := /-trace_val $-/ (((prod_form.of_expr lhs).pow (-1)) * (prod_form.of_expr rhs)).scale m,
       (sc, flp) := spec_comp_and_flipped_of_comp cmp in
   ⟨if ((bnot cl.is_less) = flp) then nsfc.pow (-1) else nsfc, sc⟩
end



meta def of_eq (lhs rhs : expr) (c : ℚ) : prod_form_comp :=
⟨(((prod_form.of_expr lhs).pow (-1)) * (prod_form.of_expr rhs)).scale c, spec_comp.eq⟩

meta def pow (pfc : prod_form_comp) (z : ℤ) : prod_form_comp :=
⟨pfc.pf.pow z, pfc.c⟩

end prod_form_comp

section proof_objs

meta inductive diseq_proof : expr → expr → ℚ → Type
| hyp : Π lhs rhs c, expr → diseq_proof lhs rhs c
| sym : Π {lhs rhs c}, Π (dp : diseq_proof lhs rhs c), diseq_proof rhs lhs (1/c)

meta mutual inductive eq_proof, ineq_proof, sign_proof, sum_form_proof
with eq_proof : expr → expr → ℚ → Type
| hyp : Π lhs rhs c, expr → eq_proof lhs rhs c
| sym : Π {lhs rhs c}, Π (ep : eq_proof lhs rhs c), eq_proof rhs lhs (1/c)
| of_opp_ineqs : Π {lhs rhs i}, Π c,
  ineq_proof lhs rhs i → ineq_proof lhs rhs (i.reverse) → eq_proof lhs rhs c
| of_sum_form_proof : Π lhs rhs c {sf}, sum_form_proof ⟨sf, spec_comp.eq⟩ → eq_proof lhs rhs c
| adhoc : Π lhs rhs c, tactic proof_sketch →  tactic expr → eq_proof lhs rhs c

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
| horiz_of_sign_proof : Π {rhs c} lhs i, sign_proof rhs c → ineq_proof lhs rhs i
| of_sum_form_proof : Π lhs rhs i {sfc}, sum_form_proof sfc → ineq_proof lhs rhs i
| adhoc : Π lhs rhs i, tactic proof_sketch → tactic expr → ineq_proof lhs rhs i

with sign_proof : expr → gen_comp → Type
| hyp  : Π e c, expr → sign_proof e c
| scaled_hyp : Π e c, expr → ℚ → sign_proof e c
| ineq_lhs : Π c, Π {lhs rhs iqp}, ineq_proof lhs rhs iqp → sign_proof lhs c
| ineq_rhs : Π c, Π {lhs rhs iqp}, ineq_proof lhs rhs iqp → sign_proof rhs c
| eq_of_two_eqs_lhs : Π {lhs rhs eqp1 eqp2}, 
    eq_proof lhs rhs eqp1 → eq_proof lhs rhs eqp2 → sign_proof lhs gen_comp.eq
| eq_of_two_eqs_rhs : Π {lhs rhs eqp1 eqp2}, 
    eq_proof lhs rhs eqp1 → eq_proof lhs rhs eqp2 → sign_proof rhs gen_comp.eq
| diseq_of_diseq_zero : Π {lhs rhs}, diseq_proof lhs rhs 0 → sign_proof lhs gen_comp.ne
| eq_of_eq_zero : Π {lhs rhs}, eq_proof lhs rhs 0 → sign_proof lhs gen_comp.eq
| eq_of_le_of_ge : Π {e}, sign_proof e gen_comp.le → sign_proof e gen_comp.ge → sign_proof e gen_comp.eq
| ineq_of_eq_and_ineq_lhs : Π {lhs rhs i c}, Π c', 
    eq_proof lhs rhs c → ineq_proof lhs rhs i →  sign_proof lhs c'
| ineq_of_eq_and_ineq_rhs : Π {lhs rhs i c}, Π c', 
    eq_proof lhs rhs c → ineq_proof lhs rhs i →  sign_proof rhs c'
| ineq_of_ineq_and_eq_zero_rhs : Π {lhs rhs i}, Π c, 
    ineq_proof lhs rhs i → sign_proof lhs gen_comp.eq → sign_proof rhs c
| diseq_of_strict_ineq : Π {e c}, sign_proof e c → sign_proof e gen_comp.ne 
| of_sum_form_proof : Π e c {sfc}, sum_form_proof sfc → sign_proof e c
| adhoc : Π e c, tactic proof_sketch → tactic expr → sign_proof e c

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

meta inductive prod_form_proof : prod_form_comp → Type
| of_ineq_proof : Π {lhs rhs iq cl cr},
    Π (id : ineq_proof lhs rhs iq) (spl : sign_proof lhs cl) (spr : sign_proof rhs cr), prod_form_proof (prod_form_comp.of_ineq lhs rhs cl cr iq)
| of_eq_proof : Π {lhs rhs c}, Π (id : eq_proof lhs rhs c) (lhsne : sign_proof lhs gen_comp.ne),
    prod_form_proof (prod_form_comp.of_eq lhs rhs c)
| of_expr_def : Π (e : expr) (pf : prod_form), prod_form_proof ⟨pf, spec_comp.eq⟩
| of_pow : Π {pfc}, Π z, prod_form_proof pfc → prod_form_proof (pfc.pow z)
| of_mul : Π {lhs rhs c1 c2}, prod_form_proof ⟨lhs, c1⟩ → prod_form_proof ⟨rhs, c2⟩ → (list Σ e : expr, sign_proof e gen_comp.ne) → prod_form_proof ⟨lhs*rhs, spec_comp.strongest c1 c2⟩ 
| adhoc : Π pfc, tactic proof_sketch → tactic expr → prod_form_proof pfc
| fake : Π pd, prod_form_proof pd

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
| .(_) .(_) .(_) (@horiz_of_sign_proof rhs c lhs iq sp) := "horiz_of_sign"
| .(_) .(_) .(_) (@of_sum_form_proof lhs rhs i _ sp) := "of_sum_form"
| .(_) .(_) .(_) (adhoc _ _ _ _ t) := "adhoc"

meta instance ineq_proof.has_to_format (lhs rhs c) : has_to_format (ineq_proof lhs rhs c) :=
⟨ineq_proof.to_format2⟩

section
open sign_proof
meta def sign_proof.to_format : Π {e c}, sign_proof e c → format
| (_) (_) (hyp _ _ _) := "hyp"
| (_) (_) (scaled_hyp _ _ _ _) := "scaled_hyp"
| (_) (_) (ineq_lhs _ _) := "ineq_lhs"
| (_) (_) (ineq_rhs _ _) := "ineq_rhs"
| (_) (_) (eq_of_two_eqs_rhs _ _) := "eq_of_two_eqs_rhs"
| (_) (_) (eq_of_two_eqs_lhs _ _) := "eq_of_two_eqs_lhs"
| (_) (_) (diseq_of_diseq_zero _) := "diseq_of_diseq_zero"
| (_) (_) (eq_of_eq_zero _) := "eq_of_eq_zero"
| (_) (_) (eq_of_le_of_ge _ _) := "eq_of_le_of_ge"
| (_) (_) (ineq_of_eq_and_ineq_lhs _ _ _) := "ineq_of_eq_and_ineq_lhs"
| (_) (_) (ineq_of_eq_and_ineq_rhs _ _ _) := "ineq_of_eq_and_ineq_rhs"
| (_) (_) (ineq_of_ineq_and_eq_zero_rhs _ _ _) := "ineq_of_ineq_and_eq_zero_rhs"
| (_) (_) (diseq_of_strict_ineq _) := "diseq_of_strict_ineq"
| (_) (_) (of_sum_form_proof _ _ _) := "of_sum_form_proof"
| (_) (_) (adhoc _ _ _ _) := "adhoc"

meta instance sign_proof.has_to_format {e c} : has_to_format (sign_proof e c) := ⟨sign_proof.to_format⟩
end

end proof_objs

section data_objs

meta structure ineq_data (lhs rhs : expr) :=
(inq : ineq)
(prf : ineq_proof lhs rhs inq)

meta def ineq_data.reverse {lhs rhs : expr} (id : ineq_data lhs rhs) : ineq_data rhs lhs :=
if id.inq.is_horiz then
 let sp := sign_proof.ineq_rhs id.inq.to_comp/-.reverse-/ id.prf in
  ⟨_, ineq_proof.zero_comp_of_sign_proof lhs id.inq.reverse sp⟩
else if id.inq.is_zero_slope then
 let sp := sign_proof.ineq_lhs id.inq.to_comp id.prf in
  ⟨_, ineq_proof.horiz_of_sign_proof rhs id.inq.reverse sp⟩
else
 ⟨id.inq.reverse, id.prf.sym⟩

meta def ineq_data.to_format {lhs rhs} : ineq_data lhs rhs → format
| ⟨inq, prf⟩ := "⟨" ++ to_fmt inq ++ " : " ++ to_fmt prf ++ "⟩"

meta instance ineq_data.has_to_format (lhs rhs) : has_to_format (ineq_data lhs rhs) :=
⟨ineq_data.to_format⟩

/-meta instance ineq_data.has_decidable_eq (lhs rhs) : decidable_eq (ineq_data lhs rhs) :=
by tactic.mk_dec_eq_instance-/

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

meta def eq_data.refl (e : expr) : eq_data e e :=
⟨1, eq_proof.adhoc e e 1 (do s ← to_string <$> tactic.pp e, return ⟨s ++ " = " ++ s, "reflexivity", []⟩) $ do (_, pr) ← tactic.solve_aux `(%%e = (1 : ℚ) * %%e) `[simp only [one_mul]], return pr⟩

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

meta def ineq_info.data {lhs rhs} : ineq_info lhs rhs → list (ineq_data lhs rhs)
| no_comps := []
| (one_comp id) := [id]
| (two_comps id1 id2) := [id1, id2]
| (equal _) := []


meta def ineq_info.mk_two_comps {lhs rhs} (id1 id2 : ineq_data lhs rhs) : ineq_info lhs rhs :=
if id2.inq.clockwise_of id1.inq then two_comps id1 id2 else two_comps id2 id1

meta instance ineq_info.inhabited (lhs rhs) : inhabited (ineq_info lhs rhs) :=
⟨no_comps⟩

meta def ineq_info.reverse {lhs rhs : expr} : ineq_info lhs rhs → ineq_info rhs lhs
| no_comps            := no_comps
| (one_comp id1)      := one_comp id1.reverse
| (two_comps id1 id2) := ineq_info.mk_two_comps id1.reverse id2.reverse
| (equal ed)          := equal ed.reverse

meta def ineq_info.to_format {lhs rhs} : ineq_info lhs rhs → format
| no_comps := "ineq_info.empty"
| (one_comp id1) := "{" ++ to_fmt id1 ++ "}"
| (two_comps id1 id2) := "{" ++ to_fmt id1 ++ " | " ++ to_fmt id2 ++ "}"
| (equal ed) := "{" ++ to_fmt ed ++ "}"

meta instance ineq_info.has_to_format (lhs rhs) : has_to_format (ineq_info lhs rhs) :=
⟨ineq_info.to_format⟩

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

meta def ineq_info.implies_eq {lhs rhs : expr} : ineq_info lhs rhs → ℚ → bool
| (equal ed) m := ed.c = m
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

meta structure prod_form_comp_data :=
(pfc : prod_form_comp) (prf : prod_form_proof pfc) (elim_list : rb_set expr)

namespace sum_form_comp_data

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

meta def prod_form_proof.to_format {pfc} (pfp : prod_form_proof pfc) : format :=
begin
cases pfp,
exact "of_ineq_proof",
exact "of_eq_proof",
exact "of_expr_def",
exact "of_pow",
exact "of_mul",
exact "adhoc",
exact "fake"
end

meta instance prod_form_proof.has_to_format {pfc} : has_to_format (prod_form_proof pfc) :=
⟨prod_form_proof.to_format⟩

private meta def sum_form.lt_core (sf1 sf2 : sum_form) : bool :=
sf1.to_list < sf2.to_list
private meta def prod_form.lt_core (pf1 pf2 : prod_form) : bool :=
pf1.coeff < pf2.coeff ∨ (pf1.coeff = pf2.coeff ∧ pf1.exps.to_list < pf2.exps.to_list)
meta def sum_form.lt : sum_form → sum_form → Prop := λ sf1 sf2, ↑(sum_form.lt_core sf1 sf2)
meta def prod_form.lt : prod_form → prod_form → Prop := λ pf1 pf2, ↑(prod_form.lt_core pf1 pf2)

meta instance sum_form.has_lt : has_lt sum_form := ⟨sum_form.lt⟩
meta instance sum_form.lt_decidable : decidable_rel sum_form.lt := by delta sum_form.lt; apply_instance
meta instance prod_form.has_lt : has_lt prod_form := ⟨prod_form.lt⟩
meta instance prod_form.lt_decidable : decidable_rel prod_form.lt := by delta prod_form.lt; apply_instance

meta def sum_form.cmp : sum_form → sum_form → ordering :=
cmp_using sum_form.lt
meta def prod_form.cmp : prod_form → prod_form → ordering :=
cmp_using prod_form.lt

meta def sum_form_comp.order : sum_form_comp → sum_form_comp → ordering
| ⟨_, spec_comp.lt⟩ ⟨_, spec_comp.le⟩ := ordering.lt
| ⟨_, spec_comp.lt⟩ ⟨_, spec_comp.eq⟩ := ordering.lt
| ⟨_, spec_comp.le⟩ ⟨_, spec_comp.eq⟩ := ordering.lt
| ⟨sf1, _⟩ ⟨sf2, _⟩ := sum_form.cmp sf1.normalize sf2.normalize

-- TODO: do we need to take elim_vars into account for this order?
meta def sum_form_comp_data.order : sum_form_comp_data → sum_form_comp_data → ordering
| ⟨sfc1, _, _⟩ ⟨sfc2, _, _⟩ := sfc1.order sfc2

meta instance : has_lt sum_form_comp_data := ⟨λ x y, sum_form_comp_data.order x y = ordering.lt⟩
meta instance : decidable_rel (@has_lt.lt sum_form_comp_data _) := λ _ _, by apply_instance

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
