import .datatypes .proof_reconstruction

namespace polya
open tactic


open proof_sketch


private meta def proof_sketch.trace_aux : string → proof_sketch → tactic string
| tab ⟨fact, reason, justifications⟩ :=
  let line := tab ++ fact ++ " : " ++ reason ++ "\n" in
  do js' ← justifications.mmap (proof_sketch.trace_aux (tab ++ "  ")),
     return $ line ++ string.join js'

meta def proof_sketch.trace (pf : proof_sketch) : tactic unit :=
do s ← proof_sketch.trace_aux "" pf, 
   trace s

meta def format_comp (lhs rhs : expr) (coeff : ℚ) (comp : string) : tactic string :=
do lhss ← to_string <$> pp lhs,
   rhss ← to_string <$> pp rhs,
   return $ lhss ++ " " ++ comp ++ " " ++ coeff.to_string ++ "*" ++ rhss

meta def make_hyp (lhs rhs : expr) (coeff : ℚ) (comp : string) : tactic proof_sketch :=
do s ← format_comp lhs rhs coeff comp,
     return ⟨s, "hypothesis", []⟩

meta def diseq_proof.sketch : Π {lhs rhs c}, diseq_proof lhs rhs c → tactic proof_sketch
| _ _ _ (diseq_proof.hyp lhs rhs c _) := make_hyp lhs rhs c "≠"
| _ _ _ (diseq_proof.sym dp) := diseq_proof.sketch dp

private meta def eq_proof.sketch_aux (is : Π {lhs rhs iq}, ineq_proof lhs rhs iq → tactic proof_sketch) (sfs : Π {sfc}, sum_form_proof sfc → tactic proof_sketch) : Π {lhs rhs c}, eq_proof lhs rhs c → tactic proof_sketch
| _ _ _ (eq_proof.hyp lhs rhs c _) := make_hyp lhs rhs c "="
| _ _ _ (eq_proof.sym ep) := eq_proof.sketch_aux ep
| lhs rhs _ (eq_proof.of_opp_ineqs c ip1 ip2) := 
  do ip1' ← is ip1, ip2' ← is ip2, s ← format_comp lhs rhs c "=",
     return ⟨s, "opposite weak inequalities", [ip1', ip2']⟩
| _ _ _ (eq_proof.of_sum_form_proof lhs rhs c sfp) := 
  do sfp' ← sfs sfp, s ← format_comp lhs rhs c "=",
     return ⟨s, "by linear arithmetic", sfp'.justifications⟩
| _ _ _ (eq_proof.adhoc lhs rhs c tac _) := tac
/-  do s ← format_comp lhs rhs c "=",
     ds ← tac,
     return ⟨s, "justification unknown", [ds]⟩-/

meta def format_ineq (lhs rhs : expr) (iq : ineq) : tactic string :=
match iq.to_slope with 
| slope.horiz := do s ← to_string <$> pp rhs, return $ s ++ " " ++ to_string (to_fmt iq.to_comp ++ " 0")
| slope.some m := format_comp lhs rhs m (to_string $ to_fmt iq.to_comp)
end

meta def format_sign (e : expr) (comp : gen_comp) : tactic string :=
do s ← to_string <$> pp e, return $ s ++ " " ++ to_string (to_fmt comp) ++ " 0"

private meta def ineq_proof.sketch_aux (ss : Π {e c}, sign_proof e c → tactic proof_sketch) (sfs : Π {sfc}, sum_form_proof sfc → tactic proof_sketch)  : Π {lhs rhs iq}, ineq_proof lhs rhs iq → tactic proof_sketch
| _ _ _ (ineq_proof.hyp lhs rhs iq _) :=
  do s ← format_ineq lhs rhs iq,
     return ⟨s, "hypothesis", []⟩ 
| _ _ _ (ineq_proof.sym ip) := ineq_proof.sketch_aux ip
| lhs rhs iq (ineq_proof.of_ineq_proof_and_diseq ip dp) := 
  do ip' ← ineq_proof.sketch_aux ip,
     dp' ← dp.sketch,
     s   ← format_ineq lhs rhs iq,
     return ⟨s, "strengthen inequality with disequality", [ip', dp']⟩
| lhs rhs iq (ineq_proof.of_ineq_proof_and_sign_lhs ip sp) := 
  do ip' ← ineq_proof.sketch_aux ip,
     sp' ← ss sp,
     s   ← format_ineq lhs rhs iq,
     return ⟨s, "implied from sign info", [ip', sp']⟩
| lhs rhs iq (ineq_proof.of_ineq_proof_and_sign_rhs ip sp) := 
  do ip' ← ineq_proof.sketch_aux ip,
     sp' ← ss sp,
     s   ← format_ineq lhs rhs iq,
     return ⟨s, "implied from sign info", [ip', sp']⟩
| lhs _ iq (ineq_proof.zero_comp_of_sign_proof rhs i sp) := ss sp
| _ _ _ (ineq_proof.horiz_of_sign_proof lhs i sp) := ss sp
| _ _ _ (ineq_proof.of_sum_form_proof lhs rhs i sfp) := 
  do sfp' ← sfs sfp,
     s    ← format_ineq lhs rhs i,
     return ⟨s, "by linear arithmetic", sfp'.justifications⟩
| _ _ _ (ineq_proof.adhoc lhs rhs i tac _) := tac 
/-  do s ← format_ineq lhs rhs i,
     return ⟨s, "justification unknown", []⟩-/

private meta def sign_proof.sketch_aux (is : Π {lhs rhs iq}, ineq_proof lhs rhs iq → tactic proof_sketch) (es : Π {lhs rhs c}, eq_proof lhs rhs c → tactic proof_sketch)  (sfs : Π {sfc}, sum_form_proof sfc → tactic proof_sketch) : Π {e c}, sign_proof e c → tactic proof_sketch
| _ _ (sign_proof.hyp e c _) := 
  do s ← format_sign e c,
     return ⟨s, "hypothesis", []⟩
| lhs _ (sign_proof.ineq_lhs c ip) :=
  do ip' ← is ip,
     s ← format_sign lhs c,
     return ⟨s, ip'.reason, ip'.justifications⟩
| rhs _ (sign_proof.ineq_rhs c ip) := 
  do ip' ← is ip,
     s ← format_sign rhs c,
     return ⟨s, ip'.reason, ip'.justifications⟩
| e c (sign_proof.eq_of_two_eqs_lhs ep1 ep2) := 
  do ep1' ← es ep1, ep2' ← es ep2,
     s    ← format_sign e c,
     return ⟨s, "eq zero of two equalities", [ep1', ep2']⟩ 
| e c (sign_proof.eq_of_two_eqs_rhs ep1 ep2) := 
  do ep1' ← es ep1, ep2' ← es ep2,
     s    ← format_sign e c,
     return ⟨s, "eq zero of two equalities", [ep1', ep2']⟩
| e c (sign_proof.diseq_of_diseq_zero dp) :=
  do dp' ← dp.sketch,
     s   ← format_sign e c,
     return ⟨s, dp'.reason, dp'.justifications⟩
| e c (sign_proof.eq_of_eq_zero ep) := 
  do ep' ← es ep,
     s   ← format_sign e c,
     return ⟨s, ep'.reason, ep'.justifications⟩
| e c (sign_proof.eq_of_le_of_ge lep gep) :=
  do lep' ← sign_proof.sketch_aux lep, 
     gep' ← sign_proof.sketch_aux gep,
     s    ← format_sign e c,
     return ⟨s, "equality of opposite inequalities", [lep', gep']⟩
| e c (sign_proof.ineq_of_eq_and_ineq_lhs c' ep ip) := 
  do ep' ← es ep,
     ip' ← is ip,
     s   ← format_sign e c,
     return ⟨s, "sign info implied by eq and ineq", [ep', ip']⟩
| e c (sign_proof.ineq_of_eq_and_ineq_rhs c' ep ip) := 
  do ep' ← es ep,
     ip' ← is ip,
     s   ← format_sign e c,
     return ⟨s, "sign info implied by eq and ineq", [ep', ip']⟩
| e c (sign_proof.ineq_of_ineq_and_eq_zero_rhs c' ip spe) := 
  do ip' ← is ip,
     spe' ← sign_proof.sketch_aux spe,
     s    ← format_sign e c,
     return ⟨s, "sign by transitivity", [ip', spe']⟩
| e c (sign_proof.diseq_of_strict_ineq sp) := 
  do sp' ← sign_proof.sketch_aux sp,
     s ← format_sign e c,
     return ⟨s, "diseq from strict ineq", [sp']⟩
| _ _ (sign_proof.of_sum_form_proof e c sfp) := 
  do sfp' ← sfs sfp,
     s    ← format_sign e c,
     return ⟨s, "by linear arithmetic", sfp'.justifications⟩
| _ _ (sign_proof.adhoc e c tac _) := tac
/-  do s ← format_sign e c,
     return ⟨s, "justification unknown", []⟩-/


meta def format_sfc (sfc : sum_form_comp) : tactic string :=
to_string <$> (sfc.to_expr >>= pp)

private meta def sum_form_proof.sketch_aux  (is : Π {lhs rhs iq}, ineq_proof lhs rhs iq → tactic proof_sketch) (es : Π {lhs rhs c}, eq_proof lhs rhs c → tactic proof_sketch) (ss : Π {e c}, sign_proof e c → tactic proof_sketch) : Π {sfc}, sum_form_proof sfc → tactic proof_sketch
| sfc (sum_form_proof.of_ineq_proof ip) := 
  do ip'  ← is ip,
     return ⟨"~", "~", [ip']⟩
| sfc (sum_form_proof.of_eq_proof ep) := 
  do ip'  ← es ep,
     return ⟨"~", "~", [ip']⟩
| sfc (sum_form_proof.of_sign_proof sp) :=
  do ip'  ← ss sp,
     return ⟨"~", "~", [ip']⟩
| sfc (sum_form_proof.of_add_factor_same_comp m sfp1 sfp2) := 
  do sfp1' ← sum_form_proof.sketch_aux sfp1, sfp2' ← sum_form_proof.sketch_aux sfp2,
     return ⟨"~", "~", sfp1'.justifications ++ sfp2'.justifications⟩
| sfc (sum_form_proof.of_add_eq_factor_op_comp m sfp1 sfp2) :=
  do sfp1' ← sum_form_proof.sketch_aux sfp1, sfp2' ← sum_form_proof.sketch_aux sfp2,
     return ⟨"~", "~", sfp1'.justifications ++ sfp2'.justifications⟩
| sfc (sum_form_proof.of_scale m sfp) := 
  sum_form_proof.sketch_aux sfp
| sfc (sum_form_proof.of_expr_def e sf) := 
  do s ← format_sfc sfc,
     return ⟨s, "expression definition", []⟩
| _ (sum_form_proof.fake sfc) :=
  do s ← format_sfc sfc,
     return ⟨s, "unjustified", []⟩

section
parameters
  (is : Π {lhs rhs iq}, ineq_proof lhs rhs iq → tactic proof_sketch) 
  (sfs : Π {sfc}, sum_form_proof sfc → tactic proof_sketch)

private meta def epr := (@eq_proof.sketch_aux @is @sfs)

private meta def spr : Π {e c}, sign_proof e c → tactic proof_sketch := sign_proof.sketch_aux @is @epr @sfs
end

section
parameters
  (is : Π {lhs rhs iq}, ineq_proof lhs rhs iq → tactic proof_sketch) 

private meta def sfpr' : unit → Π {sfc : sum_form_comp}, sum_form_proof sfc → tactic proof_sketch
| () := @sum_form_proof.sketch_aux @is (@epr @is (@sfpr' ())) (@spr @is (@sfpr' ()))

private meta def sfpr := @sfpr' ()

private meta def epr' := @epr @is @sfpr

private meta def spr' := @spr @is @sfpr
end

private meta def ineq_proof.sketch_aux' : unit → Π {lhs rhs iq}, ineq_proof lhs rhs iq → tactic proof_sketch
| () := @ineq_proof.sketch_aux (@spr' (@ineq_proof.sketch_aux' ())) (@sfpr (@ineq_proof.sketch_aux' ()))

meta def ineq_proof.sketch := @ineq_proof.sketch_aux' ()

meta def eq_proof.sketch := @epr' @ineq_proof.sketch

meta def sign_proof.sketch := @spr' @ineq_proof.sketch

meta def sum_form_proof.sketch := @sfpr @ineq_proof.sketch


meta def prod_form_proof.sketch : Π {pfc}, prod_form_proof pfc → tactic proof_sketch
| _ (prod_form_proof.of_ineq_proof id _ _) := do id' ← id.sketch, return ⟨"~", "~", [id']⟩
| _ (prod_form_proof.of_eq_proof id _) := do id' ← id.sketch, return ⟨"~", "~", [id']⟩
| _ (prod_form_proof.of_expr_def e pf) := do s ← to_string <$> (pf.to_expr >>= tactic.pp), return ⟨s ++ " = 1", "by definition", []⟩
| _ (prod_form_proof.of_pow _ pfp) := prod_form_proof.sketch pfp
| _ (prod_form_proof.of_mul pfp1 pfp2 _) := do ds1 ← prod_form_proof.sketch pfp1, ds2 ← prod_form_proof.sketch pfp2, return ⟨"~", "~", ds1.justifications ++ ds2.justifications⟩
| _ (prod_form_proof.adhoc _ t _) := t
| _ (prod_form_proof.fake _) := return ⟨"fake", "fake", []⟩

meta def contrad.sketch : contrad → tactic proof_sketch
| contrad.none := return $ mk "no contrad" "no contrad" []
| (contrad.eq_diseq ed dd) := do ed' ← ed.prf.sketch, dd' ← dd.prf.sketch, return $ mk "false" "matching equality and disequality" [ed', dd']
| (contrad.ineqs ii id) := mk "false" "contradictory inequalities" <$> (do lp ← list.cons <$> id.prf.sketch, lp' ←  ii.data.mmap (λ id', id'.prf.sketch), return $  lp lp')
| (contrad.sign sd1 sd2) := do sd1' ← sd1.prf.sketch, sd2' ← sd2.prf.sketch, return $ mk "false" "contradictory sign info" [sd1', sd2']
| (contrad.strict_ineq_self id) := do id' ← id.prf.sketch, return $ mk "false" "strict self inequality" [id']
| (contrad.sum_form sfp) := do sfp' ← sfp.sketch, return $ mk "false" "0 < 0" [sfp']

end polya
