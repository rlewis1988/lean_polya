import .blackboard
open tactic

namespace polya

meta def polya_tactic := state_t blackboard tactic

meta def nfail : polya_tactic unit := state_t.lift tactic.failed

meta instance has_coe_tac {α} : has_coe (tactic α) (polya_tactic α) :=
⟨state_t.lift⟩

meta def has_coe_bb {α} : has_coe (polya_state α) (polya_tactic α) :=
⟨λ f bb, return $ f bb⟩

end polya
