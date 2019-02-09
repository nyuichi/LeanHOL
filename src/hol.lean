-- 3. higher order logic

import moromoro

namespace hol

inductive type : Type
| base : type
| prop : type
| arrow : type → type → type
open type

variable ν : type → Type

inductive term : type → Type
| var : Π {t}, ν t → term t
| lam : Π {t₁ t₂}, (ν t₁ → term t₂) → term (arrow t₁ t₂)
| app : Π {t₁ t₂}, term (arrow t₁ t₂) → term t₁ → term t₂
| eq : Π {t}, term t → term t → term prop
open term

def Term (t : type) : Type 1 :=
Π ν, term ν t

def judgment : list type → type → Type :=
λ Γ t, list.foldr (λ t α, ν t → α) (term ν t) Γ

def Judgment (Γ : list type) (t : type) : Type 1 :=
Π ν, judgment ν Γ t

----

universe u
variable {α : Type u}

inductive mem : α → list α → Type u
| here : Π {x l}, mem x (x :: l)
| there : Π {x l y}, mem x l → mem x (y :: l)
open mem

local infix ` ∈' `:50 := mem

variables {Γ Γ₁ Γ₂ : list type} {t t₁ t₂ t₃ : type}

def subst' : Π {t : type}, term (term ν) t → term ν t
| _ (var m) := m
| _ (lam f) := lam (λ x, subst' (f (var x)))
| _ (app m₁ m₂) := app (subst' m₁) (subst' m₂)
| _ (eq m₁ m₂) := eq (subst' m₁) (subst' m₂)

namespace judgment
  def weak : Judgment Γ t₂ → Judgment (t₁ :: Γ) t₂ :=
  λ m ν x, m ν

  def var' : Π {Γ}, judgment ν (t :: Γ) t
  | [] := λ x, var x
  | (t :: Γ) := λ x y, var' x

  def var : Π {Γ}, t ∈' Γ → Judgment Γ t
  | _ here := λ ν, var' ν
  | _ (there h) := weak (var h)

  def lam' : Π {Γ}, judgment ν (t₁ :: Γ) t₂ → judgment ν Γ (arrow t₁ t₂)
  | [] m := lam (λ x, m x)
  | (t :: Γ) f := λ x, lam' (λ y, f y x)

  def lam : Judgment (t₁ :: Γ) t₂ → Judgment Γ (arrow t₁ t₂) :=
  λ m ν, lam' ν (m ν)

  def app' : Π {Γ}, judgment ν Γ (arrow t₁ t₂) → judgment ν Γ t₁ → judgment ν Γ t₂
  | [] m₁ m₂ := app m₁ m₂
  | (t :: Γ) f m := λ x, app' (f x) (m x)

  def app : Judgment Γ (arrow t₁ t₂) → Judgment Γ t₁ → Judgment Γ t₂ :=
  λ m₁ m₂ ν, app' ν (m₁ ν) (m₂ ν)

  def eq' : Π {Γ : list type}, judgment ν Γ t → judgment ν Γ t → judgment ν Γ prop
  | [] m₁ m₂ := eq m₁ m₂
  | (t :: Γ) m₁ m₂ := λ x, eq' (m₁ x) (m₂ x)

  def eq : Judgment Γ t → Judgment Γ t → Judgment Γ prop :=
  λ m₁ m₂ ν, eq' ν (m₁ ν) (m₂ ν)

  def subst''' : Π {Γ}, judgment (term ν) (t₁ :: Γ) t₂ → judgment ν Γ t₁ → judgment ν Γ t₂
  | [] m₁ m₂ := subst' ν (m₁ m₂)
  | (t :: Γ) f m := λ x, subst''' (λ x', f x' (term.var x)) (m x)

  def subst : Judgment (t₁ :: Γ) t₂ → Judgment Γ t₁ → Judgment Γ t₂ :=
  λ m₁ m₂ ν, subst''' ν (m₁ _) (m₂ ν)
end judgment
open judgment

----

def type.fold : list type → type → type :=
λ Γ t, list.foldr arrow t Γ

def judgment.to_term' : Π {Γ : list type}, judgment ν Γ t → term ν (type.fold Γ t)
| [] m := m
| (t :: Γ) f := lam (λ x, judgment.to_term' (f x))

def judgment.to_term : Judgment Γ t → Term (type.fold Γ t) :=
λ m ν, judgment.to_term' ν (m ν)

def term_subst' : term (term ν) (arrow t₁ t₂) → term ν t₁ → term (term ν) t₂
| (lam f) m := f m
| m₁ m₂ := app m₁ (var m₂)

def term.to_judgment' : Π {Γ : list type}, term (term ν) (type.fold Γ t) → judgment ν Γ t
| [] m := subst' ν m
| (t :: Γ) m := λ x, term.to_judgment' (term_subst' ν m (var x))

def term.to_judgment : Term (type.fold Γ t) → Judgment Γ t :=
λ m ν, term.to_judgment' ν (m _)

----

def domain : type → Type
| base := term ν base
| prop := term ν prop
| (arrow t₁ t₂) := domain t₁ → domain t₂

def Domain (t : type) : Type 1 :=
Π ν, domain ν t

def reify_reflect : Π (t : type), (domain ν t → term ν t) × (term ν t → domain ν t)
| base := ⟨ id, id ⟩
| prop := ⟨ id, id ⟩
| (arrow t₁ t₂) :=
   let r₁ := reify_reflect t₁ in
   let r₂ := reify_reflect t₂ in
   let reify (f : domain ν t₁ → domain ν t₂) := lam (λ x, r₂.1 (f (r₁.2 (var x)))) in
   let reflect (f : term ν (arrow t₁ t₂)) := λ x, r₂.2 (app f (r₁.1 x)) in
   ⟨reify, reflect⟩

def reify' : domain ν t → term ν t :=
λ x, (reify_reflect ν t).1 x

def reify : Domain t → Term t :=
λ x ν, reify' ν (x ν)

def eval' : Π {t : type}, term (domain ν) t → domain ν t
| _ (var x) := x
| _ (lam f) := λ x, eval' (f x)
| _ (app m₁ m₂) := (eval' m₁) (eval' m₂)
| _ (eq m₁ m₂) := eq (reify' ν (eval' m₁)) (reify' ν (eval' m₂))

def eval : Term t → Domain t :=
λ m ν, eval' ν (m _)

def normalize : Term t → Term t :=
reify ∘ eval

instance term_setoid : setoid (Term t) :=
⟨inv_image eq normalize,
 inv_image.equivalence eq normalize eq.equivalence⟩

instance judgment_setoid [h : setoid (Term (type.fold Γ t))] : setoid (Judgment Γ t) :=
⟨inv_image h.r judgment.to_term,
 inv_image.equivalence h.r judgment.to_term h.iseqv⟩

----

def type.to_string : type → string
| base := "ι"
| prop := "ο"
| (arrow t₁ t₂) := "(" ++ type.to_string t₁ ++ " → " ++ type.to_string t₂ ++ ")"

instance : has_to_string type :=
⟨type.to_string⟩

def term.to_string' : Π {t}, term (λ t, ℕ) t → ℕ → string
| _ (var n) _ := to_string n
| _ (lam f) lv := "(λ" ++ to_string lv ++ "." ++ term.to_string' (f lv) (lv + 1) ++ ")"
| _ (app m₁ m₂) lv := "(" ++ term.to_string' m₁ lv ++ " " ++ term.to_string' m₂ lv ++ ")"
| _ (eq m₁ m₂) lv := "(" ++ term.to_string' m₁ lv ++ " = " ++ term.to_string' m₂ lv ++ ")"

def term.to_string : Term t → string :=
λ m, term.to_string' (m _) 0 ++ " : " ++ to_string t

instance term_has_to_string : has_to_string (Term t) :=
⟨ term.to_string ⟩

def judgment.to_string' : Π {Γ}, judgment (λ t, ℕ) Γ t → ℕ → string
| [] m lv := "⊢ " ++ term.to_string' m lv
| (t :: Γ) f lv := "(" ++ to_string lv ++ " : " ++ to_string t ++ ") " ++ judgment.to_string' (f lv) (lv + 1)

def judgment.to_string : Judgment Γ t → string :=
λ m, judgment.to_string' (m _) 0 ++ " : " ++ to_string t

instance judgment_has_to_string : has_to_string (Judgment Γ t) :=
⟨judgment.to_string⟩

instance : has_repr (Judgment Γ t) :=
⟨judgment.to_string⟩

----

namespace term
  def top : Term prop :=
  λ ν, eq (lam (λ x : ν prop, var x)) (lam (λ x, var x))

  def and : Term (arrow prop (arrow prop prop)) :=
  λ ν, lam (λ p₁, lam (λ p₂, eq (lam (λ f : ν (arrow _ (arrow _ prop)), app (app (var f) (top ν)) (top ν))) (lam (λ f, app (app (var f) (var p₁)) (var p₂)))))

  def Forall : Term (arrow (arrow t prop) prop) :=
  λ ν, lam (λ f, eq (var f) (lam (λ x, (top ν))))

  def bot : Term prop :=
  λ ν, app (Forall ν) (lam (λ p, var p))

  def implies : Term (arrow prop (arrow prop prop)) :=
  λ ν, lam (λ p₁, lam (λ p₂, eq (app (app (and ν) (var p₁)) (var p₂)) (var p₁)))

  def not : Term (arrow prop prop) :=
  λ ν, lam (λ p, app (app (implies ν) (var p)) (bot ν))

  def iff : Term (arrow prop (arrow prop prop)):=
  λ ν, lam (λ p₁, lam (λ p₂, eq (var p₁) (var p₂)))

  def or : Term (arrow prop (arrow prop prop)) :=
  λ ν, lam (λ p₁, lam (λ p₂, app (Forall ν) (lam (λ r, app (app (implies ν) (app (app (and ν) (app (app (implies ν) (var p₁)) (var r))) (app (app (implies ν) (var p₂)) (var r)))) (var r)))))

  def Exists : Term (arrow (arrow t prop) prop) :=
  λ ν, lam (λ f, app (Forall ν) (lam (λ r, app (app (implies ν) (app (Forall ν) (lam (λ x, app (app (implies ν) (app (var f) (var x))) (var r))))) (var r))))
end term
open term

#eval @id (Judgment [] prop) $ app (app and top) (app (app or bot) top)

----

inductive proof : Π {Γ}, list (Judgment Γ prop) → Judgment Γ prop → Prop
| assump : Π {Γ Φ} {φ : Judgment Γ prop}, φ ∈ Φ → proof Φ φ
| refl : Π {Γ Φ t} {m₁ m₂ : Judgment Γ t}, m₁ ≈ m₂ → proof Φ (eq m₁ m₂)
| cong : Π {Γ Φ t} (m : Judgment (t :: Γ) prop) (m₂ m₁ : Judgment Γ t), proof Φ (eq m₁ m₂) → proof Φ (subst m m₁) → proof Φ (subst m m₂)
| prop_ext : Π {Γ Φ} {φ₁ φ₂ : Judgment Γ prop}, proof (φ₁ :: Φ) φ₂ → proof (φ₂ :: Φ) φ₁ → proof Φ (eq φ₁ φ₂)
| fun_ext : Π {Γ Φ t₁ t₂} (m₁ m₂ : Judgment (t₁ :: Γ) t₂), proof (list.map weak Φ) (eq m₁ m₂) → proof Φ (eq (lam m₁) (lam m₂))

-- Let's prove!

example : @proof [prop] [var here] (eq (weak top) (var here)) :=
begin
  apply proof.prop_ext,
  { apply proof.assump,
    simp },
  { apply proof.refl,
    refl }
end

example : @proof [prop] [eq (weak top) (var here)] (var here) :=
begin
  apply proof.cong (var here) (var here) (weak $ @id (Judgment [] prop) top),
  { apply proof.assump,
    simp },
  { apply proof.refl,
    simp }
end

example {φ₁ φ₂} {Φ : list (Judgment [] prop)} : proof Φ (app (app and φ₁) φ₂) → proof Φ φ₁ :=
begin
  intro p,
  apply proof.cong
    (var here)
    φ₁
    (λ ν, app (lam (λ f, app (app (var f) (φ₁ ν)) (φ₂ ν))) (lam (λ p₁, lam (λ p₂, var p₁)))),
  { apply proof.refl,
    funext,
    refl },
  { apply proof.cong
      (@id (Judgment [arrow _ prop] prop) $ λ ν f, app (var f) (lam (λ p₁, lam (λ p₂, var p₁))))
      (λ ν, lam (λ f, app (app (var f) (φ₁ ν)) (φ₂ ν)))
      (@id (Judgment [] (arrow _ prop)) $ λ ν, lam (λ f, app (app (var f) (top ν)) (top ν))),
    { apply proof.cong
        (var here)
        (eq
          (@id (Judgment [] (arrow _ prop)) $ λ ν, lam (λ f, app (app (var f) (top ν)) (top ν)))
          (λ ν, lam (λ f, app (app (var f) (φ₁ ν)) (φ₂ ν))))
        (λ ν, app (app (lam (λ p₁, lam (λ p₂, eq (lam (λ f : ν (arrow _ (arrow _ prop)), app (app (var f) (top ν)) (top ν))) (lam (λ f, app (app (var f) (var p₁)) (var p₂)))))) (φ₁ ν)) (φ₂ ν)),
      { apply proof.refl,
        funext,
        refl },
      { from p } },
    { apply proof.cong
        (var here)
        (@id (Judgment [] _) $ λ ν, app (lam (λ f, app (app (var f) (top ν)) (top ν))) (lam (λ p₁, lam (λ p₂, var p₁))))
        top,
      { apply proof.refl,
        funext,
        refl },
      { apply proof.refl,
        refl } } }
end

end hol