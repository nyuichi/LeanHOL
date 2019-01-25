-- 2. simply typed lambda calculus

import moromoro

@[derive decidable_eq]
inductive type : Type
| base : type
| arrow : type → type → type
open type

def type.to_string : type → string
| base := "ι"
| (arrow t₁ t₂) := "(" ++ type.to_string t₁ ++ " → " ++ type.to_string t₂ ++ ")"

instance : has_to_string type :=
⟨type.to_string⟩

#eval to_string (arrow (arrow base base) base)

----

variable ν : type → Type

inductive preterm : type → Type
| var : Π {t}, ν t → preterm t
| lam : Π {t₁ t₂}, (ν t₁ → preterm t₂) → preterm (arrow t₁ t₂)
| app : Π {t₁ t₂}, preterm (arrow t₁ t₂) → preterm t₁ → preterm t₂
open preterm

def Preterm (t : type) : Type 1 :=
Π ν, preterm ν t

def preterm.to_string' : Π {t : type}, preterm (λ t, ℕ) t → ℕ → string
| _ (var n) _ := to_string n
| _ (lam f) lv := "(λ" ++ to_string lv ++ "." ++ preterm.to_string' (f lv) (lv + 1) ++ ")"
| _ (app m₁ m₂) lv := "(" ++ preterm.to_string' m₁ lv ++ " " ++ preterm.to_string' m₂ lv ++ ")"

def preterm.to_string {t : type} : Preterm t → string :=
λ m, preterm.to_string' (m _) 0 ++ " : " ++ to_string t

instance {t : type} : has_to_string (Preterm t) :=
⟨ preterm.to_string ⟩

def type.nat := arrow (arrow base base) (arrow base base)

def zero : Preterm type.nat :=
λ ν, lam (λ f, lam (λ x, var x))

def succ : Preterm (arrow type.nat type.nat) :=
λ ν, lam (λ n, lam (λ f, lam (λ x, app (var f) (app (app (var n) (var f)) (var x)))))

def succ_zero : Preterm type.nat :=
(λ ν, app (succ ν) (zero ν))

#eval to_string zero      -- "(λ0.(λ1.1)) : ((ι → ι) → (ι → ι))"
#eval to_string succ      -- "(λ0.(λ1.(λ2.(1 ((0 1) 2))))) : (((ι → ι) → (ι → ι)) → ((ι → ι) → (ι → ι)))"
#eval to_string succ_zero -- "((λ0.(λ1.(λ2.(1 ((0 1) 2))))) (λ0.(λ1.1))) : ((ι → ι) → (ι → ι))"

-- // error!
-- def ω : Preterm _ := -- no such type
-- λ ν, lam (λ x, app (var x) (var x))

----

-- def term0 (t : type) := Π ν, preterm ν t
-- def term1 (t₁ t₂ : type) := Π ν, ν t₁ → preterm ν t₂ -- preterm with one free variable

-- inductive term : list type → type → Type
-- | empty : Π {t}, preterm ν t → term [] t
-- | extend : Π {t₁ t₂ Γ}, (ν t₁ → term Γ t₂) → term (t₁ :: Γ) t₂

def term : list type → type → Type :=
λ Γ t, list.foldr (λ t α, ν t → α) (preterm ν t) Γ

def Term (Γ : list type) (t : type) : Type 1 := -- Type 1
Π ν, term ν Γ t

#reduce Term [] base           -- Π ν, preterm ν base
#reduce Term [base] base       -- Π ν, ν base → preterm ν base
#reduce Term [base, base] base -- Π ν, ν base → ν base → preterm ν base

variables {Γ : list type} {t : type}

def term.to_string' : Π {Γ : list type}, term (λ t, ℕ) Γ t → ℕ → string
| [] m lv := "⊢ " ++ preterm.to_string' m lv
| (t :: Γ) f lv := "(" ++ to_string lv ++ " : " ++ to_string t ++ ") " ++ term.to_string' (f lv) (lv + 1)

def term.to_string : Term Γ t → string :=
λ m, term.to_string' (m _) 0 ++ " : " ++ to_string t

instance : has_to_string (Term Γ t) :=
⟨term.to_string⟩

def ex1 : Term [arrow base base, base] (arrow base base) :=
λ ν, λ x₁ x₂, lam (λ y, var x₂)

#eval to_string ex1 -- "(0 : (ι → ι)) (1 : ι) ⊢ (λ2.1) : (ι → ι)"

---- 

variables {t₁ t₂ : type}

def subst' : Π {t : type}, preterm (preterm ν) t → preterm ν t
| _ (var m) := m
| _ (lam f) := lam (λ x, subst' (f (var x)))
| _ (app m₁ m₂) := app (subst' m₁) (subst' m₂)

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

-----

variables {Γ₁ Γ₂ : list type}

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

def term.contr : Term (t₁ :: t₁ :: Γ) t₂ → Term (t₁ :: Γ) t₂ :=
λ m, term.subst m term.var0 -- corollary

def term.weaken1 : Term Γ t₂ → Term (t₁ :: Γ) t₂ :=
λ m ν x, m ν

def term.weaken' : Π {Γ₂ : list type}, Term Γ₁ t → Term (Γ₂ ++ Γ₁) t
| [] m := m
| (t :: Γ) m := term.weaken1 (term.weaken' m)

def term.weaken : Term Γ₁ t → Term (Γ₂ ++ Γ₁) t :=
term.weaken'

def term.var₁ : Term (Γ₁ ++ t ::  Γ₂) t :=
term.weaken term.var0

inductive perm {α : Type} : list α → list α → Type -- proof relevant version
| nil   : perm [] []
| skip  : Π (x : α) {l₁ l₂ : list α}, perm l₁ l₂ → perm (x :: l₁) (x :: l₂)
| swap  : Π (x y : α) (l : list α), perm (y :: x :: l) (x :: y :: l)
| trans : Π {l₁ l₂ l₃ : list α}, perm l₁ l₂ → perm l₂ l₃ → perm l₁ l₃

infix ~ := perm

def term.exchange' : Π {Γ₁ Γ₂ : list type}, (Γ₁ ~ Γ₂) → term ν Γ₁ t → term ν Γ₂ t
| _ _ perm.nil m := m
| _ _ (perm.skip _ h) m := λ x, term.exchange' h (m x)
| _ _ (perm.swap _ _ _) m := λ x₁ x₂, m x₂ x₁
| _ _ (perm.trans h₁ h₂) m := term.exchange' h₂ (term.exchange' h₁ m)

def term.exchange : (Γ₁ ~ Γ₂) → Term Γ₁ t → Term Γ₂ t :=
λ h m ν, term.exchange' ν h (m ν)

def term.var₂ : (t :: Γ₁ ~ Γ₂) → Term Γ₂ t :=
λ h, term.exchange h term.var0

-- def type.has_dec_eq : decidable_eq type
-- | base base := is_true rfl
-- | (arrow t₁ t₂) base := is_false (λ h, type.no_confusion h)
-- | base (arrow t₁ t₂) := is_false (λ h, type.no_confusion h)
-- | (arrow t₁ t₂) (arrow s₁ s₂) :=
--   match type.has_dec_eq t₁ s₁ with
--   | (is_true h) :=
--     match type.has_dec_eq t₂ s₂ with
--     | (is_true h') := is_true (h' ▸ h ▸ rfl)
--     | (is_false h') := is_false (λ h'', type.no_confusion h'' (λ h₁ h₂, absurd h₂ h'))
--     end
--   | (is_false h) := is_false (λ h', type.no_confusion h' (λ h₁ h₂, absurd h₁ h))
--   end

-- instance type_dec_eq : decidable_eq type :=
-- --type.has_dec_eq
-- by tactic.mk_dec_eq_instance

def term.var' : Π {Γ}, (t ∈ Γ) → Term Γ t
| [] h := begin rw list.mem_nil_iff at h, exfalso, assumption end
| (t' :: ts) h :=
  match type.decidable_eq t t' with
  | (is_true h') := by rw h'; exact term.var0
  | (is_false h') := term.weaken1 $ @term.var' ts begin
      rw list.mem_cons_iff at h,
      cases h with h₁ h₂,
      { exact absurd h₁ h' },
      { assumption }
    end
  end

def term.var : (t ∈ Γ) → Term Γ t :=
term.var'

def term.nonfree₁' : Π {t : type}, preterm (λ t, Prop) t → Prop
| _ (var x) := x
| _ (lam f) := term.nonfree₁' (f true)
| _ (app m₁ m₂) := term.nonfree₁' m₁ ∧ term.nonfree₁' m₂

def term.nonfree₁'' : Π {Γ : list type}, term (λ t, Prop) (t₁ :: Γ) t₂ → Prop
| [] m := term.nonfree₁' (m false)
| (t :: Γ) m := term.nonfree₁'' (λ x, m x true)

def term.nonfree₁ : Term (t₁ :: Γ) t₂ → Prop :=
λ m, term.nonfree₁'' (m _)

-- def term.free' : Π {t : type}, preterm (λ t, Prop) t → Prop
-- | _ (var x) := x
-- | _ (lam f) := term.free' (f true)
-- | _ (app m₁ m₂) := term.free' m₁ ∧ term.free' m₂
-- | _ (id m₁ m₂) := term.free' m₁ ∧ term.free' m₂

-- def term.free'' : Π {Γ : list type}, term (λ t, Prop) (t₁ :: Γ) t₂ → Prop
-- | [] m := term.free' (m false)
-- | (t :: Γ) m := term.free'' (λ x, m x true)

-- def term.free : Term (t₁ :: Γ) t₂ → Prop :=
-- λ m, term.free'' (m _)

def term.nonfree₂ (m : Term (t₁ :: Γ) t₂) : Prop :=
∃ m', m = term.weaken1 m'

lemma nonfree_var_lem (m : Term (t₁ :: Γ) t₂)
: term.nonfree₂ m ↔ ∃ (m' : Term Γ t₂), ∀ ν, (λ x, (m ν) x) = (λ x, (m' ν)) :=
begin
  unfold term.nonfree₂,
  split,
  { intro h,
    induction h,
    existsi h_w,
    intro ν,
    rw h_h,
    refl },
  { intro h,
    induction h,
    existsi h_w,
    apply funext h_h }
end

def term.nonfree (m : Term (t₁ :: Γ) t₂) := -- proof relevant version
{ m' : Term Γ t₂ // m = term.weaken1 m' }

----

def domain : type → Type
| base := preterm ν base
| (arrow t₁ t₂) := domain t₁ → domain t₂

def Domain (t : type) : Type 1 :=
Π ν, domain ν t

-- mutual def reify', reflect'
-- with reify' : Π {t : type}, domain ν t → preterm ν t
-- | base ν := v
-- | (arrow t₁ t₂) f := lam (λ x, reify' (f (reflect' (var x))))
-- with reflect' : Π {t : type}, preterm ν t → domain ν t
-- | base m := m
-- | (arrow t₁ t₂) f := λ x, reflect' (app f (reify' x))

def preterm.reify_reflect : Π {t : type}, (domain ν t → preterm ν t) × (preterm ν t → domain ν t)
| base := ⟨ id, id ⟩
| (arrow t₁ t₂) :=
   let r₁ := @preterm.reify_reflect t₁ in
   let r₂ := @preterm.reify_reflect t₂ in
   let reify (f : domain ν t₁ → domain ν t₂) := lam (λ x, r₂.1 (f (r₁.2 (var x)))) in
   let reflect (f : preterm ν (arrow t₁ t₂)) := λ x, r₂.2 (app f (r₁.1 x)) in
   ⟨reify, reflect⟩

def preterm.reify : Domain t → Preterm t :=
λ x ν, (preterm.reify_reflect ν).1 (x ν)

def preterm.reflect : Preterm t → Domain t :=
λ x ν, (preterm.reify_reflect ν).2 (x ν)

def preterm.eval' : Π {t : type}, preterm (domain ν) t → (domain ν t)
| _ (var x) := x
| _ (lam f) := λ x, preterm.eval' (f x)
| _ (app m₁ m₂) := (preterm.eval' m₁) (preterm.eval' m₂)

def preterm.eval : Preterm t → Domain t :=
λ m ν, preterm.eval' ν (m _)

def preterm.normalize : Preterm t → Preterm t :=
preterm.reify ∘ preterm.eval

def term.normalize : Term Γ t → Term Γ t :=
preterm.to_term ∘ preterm.normalize ∘ term.to_preterm

def term.zero : Term [] (arrow (arrow base base) (arrow base base)) :=
λ ν, lam (λ f, lam (λ x, var x))

def term.succ : Term [] (arrow (arrow (arrow base base) (arrow base base)) (arrow (arrow base base) (arrow base base))) :=
λ ν, lam (λ n, lam (λ f, lam (λ x, app (var f) (app (app (var n) (var f)) (var x)))))

#eval to_string $ term.normalize term.zero
#eval to_string $ term.normalize (term.app term.succ zero)
#eval to_string $ term.normalize (term.app term.succ (term.app term.succ term.zero))
#eval to_string $ term.normalize (term.app term.succ (term.app term.succ (term.app term.succ term.zero)))

def i_nat : Term [] (arrow (arrow base base) (arrow base base)) :=
λ ν, lam (λ f, var f)

#eval to_string i_nat
#eval to_string $ term.normalize i_nat

instance : setoid (Term Γ t) :=
⟨inv_image eq term.normalize,
 inv_image.equivalence eq term.normalize eq.equivalence⟩

def term.one : Term [] (arrow (arrow base base) (arrow base base)) :=
λ ν, lam (λ f, lam (λ x, app (var f) (var x)))

lemma zero_approx_zero : term.zero ≈ term.zero :=
by reflexivity

lemma succ_zero_approx_one : term.app term.succ term.zero ≈ term.one :=
begin
  unfold has_equiv.equiv setoid.r inv_image,
  reflexivity
end