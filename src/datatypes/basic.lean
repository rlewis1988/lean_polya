import data.hash_map data.complex.basic rat_additions

def {u v} hash_map.ifind {α : Type u} {β : α → Type v} [decidable_eq α] (m : hash_map α β) (a : α) [inhabited (β a)] : β a :=
match m.find a with
| none := default _
| some b := b
end
