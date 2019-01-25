-- things not defined in the standard library (but which should be)

universes u v

variables {α : Sort u} {β : Sort v}

lemma inv_image.equivalence (r : β → β → Prop) (f : α → β) (h : equivalence r) : equivalence (inv_image r f) :=
mk_equivalence _
(by intro x; apply h.1)
(by intros x y; apply h.2.1)
(by intros x y z; apply h.2.2)

lemma eq.equivalence : equivalence (@eq α) :=
mk_equivalence _ eq.refl (@eq.symm _) (@eq.trans _)
