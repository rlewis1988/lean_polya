import data.hash_map data.complex.basic rat_additions

#check list.reduce_option

#check list.filter
meta def list.bfilter {α} (p : α → bool) : list α → list α :=
list.filter (λ a, ↑(p a))

namespace hash_map
def {u v} ifind {α : Type u} {β : α → Type v} [decidable_eq α] (m : hash_map α β) (a : α) [inhabited (β a)] : β a :=
match m.find a with
| none := default _
| some b := b
end
end hash_map
