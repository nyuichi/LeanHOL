-- 3. higher order logic

import moromoro

@[derive decidable_eq]
inductive type : Type
| base : type
| prop : type
| arrow : type → type → type
open type

variable ν : type → Type

inductive preterm : type → Type
| var : Π {t}, ν t → preterm t
| lam : Π {t₁ t₂}, (ν t₁ → preterm t₂) → preterm (arrow t₁ t₂)
| app : Π {t₁ t₂}, preterm (arrow t₁ t₂) → preterm t₁ → preterm t₂
| id : Π {t}, preterm t → preterm t → preterm prop
open preterm

def Preterm (t : type) : Type 1 :=
Π ν, preterm ν t

def term : list type → type → Type :=
λ Γ t, list.foldr (λ t α, ν t → α) (preterm ν t) Γ

def Term (Γ : list type) (t : type) : Type 1 :=
Π ν, term ν Γ t

----

variables {Γ : list type} {t : type}

def type.to_string : type → string
| base := "ι"
| prop := "ο"
| (arrow t₁ t₂) := "(" ++ type.to_string t₁ ++ " → " ++ type.to_string t₂ ++ ")"

instance : has_to_string type :=
⟨type.to_string⟩

def preterm.to_string' : Π {t}, preterm (λ t, ℕ) t → ℕ → string
| _ (var n) _ := to_string n
| _ (lam f) lv := "(λ" ++ to_string lv ++ "." ++ preterm.to_string' (f lv) (lv + 1) ++ ")"
| _ (app m₁ m₂) lv := "(" ++ preterm.to_string' m₁ lv ++ " " ++ preterm.to_string' m₂ lv ++ ")"
| _ (id m₁ m₂) lv := "(" ++ preterm.to_string' m₁ lv ++ " = " ++ preterm.to_string' m₂ lv ++ ")"

def preterm.to_string : Preterm t → string :=
λ m, preterm.to_string' (m _) 0 ++ " : " ++ to_string t

instance : has_to_string (Preterm t) :=
⟨ preterm.to_string ⟩

def term.to_string' : Π {Γ}, term (λ t, ℕ) Γ t → ℕ → string
| [] m lv := "⊢ " ++ preterm.to_string' m lv
| (t :: Γ) f lv := "(" ++ to_string lv ++ " : " ++ to_string t ++ ") " ++ term.to_string' (f lv) (lv + 1)

def term.to_string : Term Γ t → string :=
λ m, term.to_string' (m _) 0 ++ " : " ++ to_string t

instance : has_to_string (Term Γ t) :=
⟨term.to_string⟩

instance : has_repr (Term Γ t) :=
⟨term.to_string⟩

----

variables {Γ₁ Γ₂ : list type} {t₁ t₂ t₃ : type}

def subst' : Π {t : type}, preterm (preterm ν) t → preterm ν t
| _ (var m) := m
| _ (lam f) := lam (λ x, subst' (f (var x)))
| _ (app m₁ m₂) := app (subst' m₁) (subst' m₂)
| _ (id m₁ m₂) := id (subst' m₁) (subst' m₂)

def type.fold : list type → type → type :=
λ Γ t, list.foldr arrow t Γ

def term.to_preterm' : Π {Γ : list type}, term ν Γ t → preterm ν (type.fold Γ t)
| [] m := m
| (t :: Γ) f := lam (λ x, term.to_preterm' (f x))

def term.to_preterm : Term Γ t → Preterm (type.fold Γ t) :=
λ m ν, term.to_preterm' ν (m ν)

def preterm_subst' : preterm (preterm ν) (arrow t₁ t₂) → preterm ν t₁ → preterm (preterm ν) t₂
| (lam f) m := f m
| m₁ m₂ := app m₁ (var m₂)

def preterm.to_term' : Π {Γ : list type}, preterm (preterm ν) (type.fold Γ t) → term ν Γ t
| [] m := subst' ν m
| (t :: Γ) m := λ x, preterm.to_term' (preterm_subst' ν m (var x))

def preterm.to_term : Preterm (type.fold Γ t) → Term Γ t :=
λ m ν, preterm.to_term' ν (m _)

----

def term.subst' : Π {Γ}, term (preterm ν) (t₁ :: Γ) t₂ → term ν Γ t₁ → term ν Γ t₂
| [] m₁ m₂ := subst' ν (m₁ m₂)
| (t :: Γ) f m := λ x, term.subst' (λ x', f x' (var x)) (m x)

def term.subst : Term (t₁ :: Γ) t₂ → Term Γ t₁ → Term Γ t₂ :=
λ m₁ m₂ ν, term.subst' ν (m₁ (preterm ν)) (m₂ ν)

def term.abs' : Π {Γ}, term ν (t₁ :: Γ) t₂ → term ν Γ (arrow t₁ t₂)
| [] m := lam (λ x, m x)
| (t :: Γ) f := λ x, term.abs' (λ y, f y x)

def term.abs : Term (t₁ :: Γ) t₂ → Term Γ (arrow t₁ t₂) :=
λ m ν, term.abs' ν (m ν)

def term.app' : Π {Γ}, term ν Γ (arrow t₁ t₂) → term ν Γ t₁ → term ν Γ t₂
| [] m₁ m₂ := app m₁ m₂
| (t :: Γ) f m := λ x, term.app' (f x) (m x)

def term.app : Term Γ (arrow t₁ t₂) → Term Γ t₁ → Term Γ t₂ :=
λ m₁ m₂ ν, term.app' ν (m₁ ν) (m₂ ν)

def term.var0' : Π {Γ}, term ν (t :: Γ) t
| [] := λ x, var x
| (t :: Γ) := λ x y, term.var0' x

def term.var0 : Term (t :: Γ) t :=
λ ν, term.var0' ν

def term.weaken1 : Term Γ t₂ → Term (t₁ :: Γ) t₂ :=
λ m ν x, m ν

def term.weaken : Π {Γ₂ : list type}, Term Γ₁ t → Term (Γ₂ ++ Γ₁) t
| [] m := m
| (t :: Γ) m := term.weaken1 (term.weaken m)

def term.var' : Π {Γ}, (t ∈ Γ) → Term Γ t
| [] h := begin rw list.mem_nil_iff at h, exfalso, assumption end
| (t' :: Γ) h :=
  match type.decidable_eq t t' with
  | (is_true h') := by rw h'; exact term.var0
  | (is_false h') := term.weaken1 $ term.var' begin
      rw list.mem_cons_iff at h,
      cases h with h₁ h₂,
      { exact absurd h₁ h' },
      { assumption }
    end
  end

def term.var : (t ∈ Γ) → Term Γ t :=
term.var'

def term.id' : Π {Γ : list type}, term ν Γ t → term ν Γ t → term ν Γ prop
| [] m₁ m₂ := id m₁ m₂
| (t :: Γ) m₁ m₂ := λ x, term.id' (m₁ x) (m₂ x)

def term.id : Term Γ t → Term Γ t → Term Γ prop :=
λ m₁ m₂ ν, term.id' ν (m₁ ν) (m₂ ν)

-----

def domain : type → Type
| base := preterm ν base
| prop := preterm ν prop
| (arrow t₁ t₂) := domain t₁ → domain t₂

def Domain (t : type) : Type 1 :=
Π ν, domain ν t

def preterm.reify_reflect : Π {t : type}, (domain ν t → preterm ν t) × (preterm ν t → domain ν t)
| base := ⟨ id, id ⟩
| prop := ⟨ id, id ⟩
| (arrow t₁ t₂) :=
   let r₁ := @preterm.reify_reflect t₁ in
   let r₂ := @preterm.reify_reflect t₂ in
   let reify (f : domain ν t₁ → domain ν t₂) := lam (λ x, r₂.1 (f (r₁.2 (var x)))) in
   let reflect (f : preterm ν (arrow t₁ t₂)) := λ x, r₂.2 (app f (r₁.1 x)) in
   ⟨reify, reflect⟩

def preterm.reify' : domain ν t → preterm ν t :=
λ x, (preterm.reify_reflect ν).1 x

def preterm.reify : Domain t → Preterm t :=
λ m ν, preterm.reify' ν (m _)

def preterm.reflect' : preterm ν t → domain ν t :=
λ x, (preterm.reify_reflect ν).2 x

def preterm.reflect : Preterm t → Domain t :=
λ x ν, preterm.reflect' ν (x _)

def preterm.eval' : Π {t : type}, preterm (domain ν) t → (domain ν t)
| _ (var x) := x
| _ (lam f) := λ x, preterm.eval' (f x)
| _ (app m₁ m₂) := (preterm.eval' m₁) (preterm.eval' m₂)
| _ (id m₁ m₂) := id (preterm.reify' ν (preterm.eval' m₁)) (preterm.reify' ν (preterm.eval' m₂))

def preterm.eval : Preterm t → Domain t :=
λ m ν, preterm.eval' ν (m _)

def preterm.normalize : Preterm t → Preterm t :=
preterm.reify ∘ preterm.eval

def term.normalize : Term Γ t → Term Γ t :=
preterm.to_term ∘ preterm.normalize ∘ term.to_preterm

instance : setoid (Term Γ t) :=
⟨inv_image eq term.normalize,
 inv_image.equivalence eq term.normalize eq.equivalence⟩

--------

def weaken : Term [] t → Term Γ t :=
λ m, by rw ←list.append_nil Γ; from term.weaken m

def term.top : Term Γ prop :=
weaken $ λ ν, id (lam (λ x : ν prop, var x)) (lam (λ x, var x))

def term.and : Term Γ (arrow prop (arrow prop prop)) :=
weaken $ λ ν, lam (λ p₁, lam (λ p₂, id (lam (λ f : ν (arrow _ (arrow _ prop)), app (app (var f) (@term.top [] ν)) (@term.top [] ν))) (lam (λ f, app (app (var f) (var p₁)) (var p₂)))))

def term.forall : Term Γ (arrow (arrow t prop) prop) :=
weaken $ λ ν, lam (λ f, id (var f) (lam (λ x, (@term.top [] ν))))

def term.bot : Term Γ prop :=
weaken $ λ ν, app (@term.forall [] _ ν) (lam (λ p, var p))

def term.implies : Term Γ (arrow prop (arrow prop prop)) :=
weaken $ λ ν, lam (λ p₁, lam (λ p₂, id (app (app (@term.and [] ν) (var p₁)) (var p₂)) (var p₁)))

def term.not : Term Γ (arrow prop prop) :=
weaken $ λ ν, lam (λ p, app (app (@term.implies [] ν) (var p)) (@term.bot [] ν))

def term.iff : Term Γ (arrow prop (arrow prop prop)):=
weaken $ λ ν, lam (λ p₁, lam (λ p₂, id (var p₁) (var p₂)))

def term.or : Term Γ (arrow prop (arrow prop prop)) :=
weaken $ λ ν, lam (λ p₁, lam (λ p₂, app (@term.forall [] _ ν) (lam (λ r, app (app (@term.implies [] ν) (app (app (@term.and [] ν) (app (app (@term.implies [] ν) (var p₁)) (var r))) (app (app (@term.implies [] ν) (var p₂)) (var r)))) (var r)))))

def term.exists : Term Γ (arrow (arrow t prop) prop) :=
weaken $ λ ν, lam (λ f, app (@term.forall [] _ ν) (lam (λ r, app (app (@term.implies [] ν) (app (@term.forall [] _ ν) (lam (λ x, app (app (@term.implies [] ν) (app (var f) (var x))) (var r))))) (var r))))

#eval (term.app (term.app term.and term.top) (term.app (term.app term.or term.bot) term.top) : Term [] prop)

----

inductive proof : Π {Γ}, list (Term Γ prop) → Term Γ prop → Prop
| assump : Π {Γ} (Φ : list (Term Γ prop)) (φ : Term Γ prop) {h : φ ∈ Φ}, proof Φ φ
| refl : Π {Γ} (Φ : list (Term Γ prop)) {t} (m₁ m₂ : Term Γ t) {h : m₁ ≈ m₂}, proof Φ (term.id m₁ m₂)
| cong : Π {Γ} (Φ : list (Term Γ prop)) {t} {m₁ m₂ : Term Γ t} (m : Term (t :: Γ) prop), proof Φ (term.id m₁ m₂) → proof Φ (term.subst m m₁) → proof Φ (term.subst m m₂)
| propext : Π {Γ} (Φ : list (Term Γ prop)) {φ₁ φ₂ : Term Γ prop}, proof (φ₁ :: Φ) φ₂ → proof (φ₂ :: Φ) φ₁ → proof Φ (term.id φ₁ φ₂)
| funext : Π {Γ} (Φ : list (Term Γ prop)) {t₁ t₂} {m₁ m₂ : Term (t₁ :: Γ) t₂}, proof (list.map term.weaken1 Φ) (term.id m₁ m₂) → proof Φ (term.id (term.abs m₁) (term.abs m₂))

example : @proof [prop] [term.var0] (term.id term.top term.var0) :=
begin
  apply proof.propext,
  { apply proof.assump,
    simp },
  { apply proof.refl,
    refl }
end

example : @proof [prop] [term.id term.top term.var0] term.var0 :=
begin
  change @proof [prop] [term.id term.top term.var0] (term.subst term.var0 term.var0),
  apply @proof.cong _ _ _ term.top,
  { apply proof.assump,
    simp },
  { change @proof [prop] [term.id term.top term.var0] term.top,
    apply proof.refl,
    simp }
end

example {φ₁ φ₂} : @proof [] [] (term.app (term.app term.and φ₁) φ₂) → @proof [] [] φ₁ :=
begin
  intro p,
  change @proof [] [] (term.subst term.var0 φ₁),
  let q : Term [] prop := λ ν, app (lam (λ f, app (app (var f) (φ₁ ν)) (φ₂ ν))) (lam (λ p₁, lam (λ p₂, var p₁))),
  apply @proof.cong _ _ _ q,
  { apply proof.refl,
    funext,
    refl },
  { change @proof [] [] q,
    let m₁ : Term [arrow (arrow prop (arrow prop prop)) prop] prop := λ ν f, app (var f) (lam (λ p₁, lam (λ p₂, var p₁))),
    let m₂ : Term [] _ := λ ν, lam (λ f, app (app (var f) (φ₁ ν)) (φ₂ ν)),
    change @proof [] [] (term.subst m₁ m₂),
    let m₃ : Term [] (arrow (arrow prop (arrow prop prop)) prop) := λ ν, lam (λ f, app (app (var f) (@term.top [] ν)) (@term.top [] ν)),
    apply @proof.cong _ _ _ m₃,
    { clear q m₁,
      unfold term.app term.and weaken term.weaken term.app' at p,
      let m₄ : Term [] prop := λ ν, app (app (lam (λ p₁, lam (λ p₂, id (lam (λ f : ν (arrow _ (arrow _ prop)), app (app (var f) (@term.top [] ν)) (@term.top [] ν))) (lam (λ f, app (app (var f) (var p₁)) (var p₂)))))) (φ₁ ν)) (φ₂ ν),
      change @proof [] [] (term.subst term.var0 (term.id m₃ m₂)),
      apply @proof.cong _ _ _ m₄,
      { apply proof.refl,
        unfold has_equiv.equiv setoid.r inv_image,
        simp [m₄, m₂, m₃],
        funext,
        refl },
      { change @proof [] [] m₄,
        simp [m₄],
        from p } },
    { let m₅ := λ ν, app (lam (λ f, app (app (var f) (@term.top [] ν)) (@term.top [] ν))) (lam (λ p₁, lam (λ p₂, var p₁))),
      let m₆ := λ ν, @term.top [] ν,
      change @proof [] [] (term.subst term.var0 m₅),
      apply @proof.cong _ _ _ m₆,
      { apply proof.refl,
        simp [m₅, m₆],
        funext,
        refl },
      { change @proof [] [] (@term.top []),
        apply proof.refl,
        refl } } },
end
