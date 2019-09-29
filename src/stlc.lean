-- 2. simply typed lambda calculus

import moromoro
import logic.basic

namespace stlc

inductive type : Type
| base : type
| arrow : type → type → type
open type

def type.repr : type → string
| base := "ι"
| (arrow t₁ t₂) := "(" ++ type.repr t₁ ++ " → " ++ type.repr t₂ ++ ")"

instance type_has_repr : has_repr type :=
⟨type.repr⟩

#eval (arrow (arrow base base) base)

----

variables ν : type → Type

inductive term : type → Type
| var : Π {t}, ν t → term t
| lam : Π {t₁ t₂}, (ν t₁ → term t₂) → term (arrow t₁ t₂)
| app : Π {t₁ t₂}, term (arrow t₁ t₂) → term t₁ → term t₂
open term

def Term (t : type) : Type 1 :=
Π ν, term ν t

variables {t t₁ t₂ t₃ : type}

def term.repr' : Π {t : type}, term (λ t, ℕ) t → ℕ → string
| _ (var n) _ := repr n
| _ (lam f) lv := "(λ" ++ repr lv ++ "." ++ term.repr' (f lv) (lv + 1) ++ ")"
| _ (app m₁ m₂) lv := "(" ++ term.repr' m₁ lv ++ " " ++ term.repr' m₂ lv ++ ")"

def term.repr : Term t → string :=
λ m, term.repr' (m _) 0 ++ " : " ++ repr t

instance Term_has_repr : has_repr (Term t) :=
⟨ term.repr ⟩

def nat : type := arrow (arrow base base) (arrow base base)

def zero : Term nat :=
λ ν, lam (λ f, lam (λ x, var x))

def succ : Term (arrow nat nat) :=
λ ν, lam (λ n, lam (λ f, lam (λ x, app (var f) (app (app (var n) (var f)) (var x)))))

def App : Term (arrow t₁ t₂) → Term t₁ → Term t₂ :=
λ m₁ m₂ ν, app (m₁ ν) (m₂ ν)

def succ_zero : Term nat :=
App succ zero

#eval zero
--> (λ0.(λ1.1)) : ((ι → ι) → (ι → ι))
#eval succ
--> (λ0.(λ1.(λ2.(1 ((0 1) 2))))) : (((ι → ι) → (ι → ι)) → ((ι → ι) → (ι → ι)))
#eval succ_zero
--> ((λ0.(λ1.(λ2.(1 ((0 1) 2))))) (λ0.(λ1.1))) : ((ι → ι) → (ι → ι))

-- -- // error!
-- def ω : Term _ := -- no such type
-- λ ν, lam (λ x, app (var x) (var x))

----

def domain : type → Type
| base := term ν base
| (arrow t₁ t₂) := domain t₁ → domain t₂

def Domain (t : type) : Type 1 :=
Π ν, domain ν t

def eval' : Π {t : type}, term (domain ν) t → domain ν t
| _ (var x) := x
| _ (lam f) := λ x, eval' (f x)
| _ (app m₁ m₂) := (eval' m₁) (eval' m₂)

def eval : Term t → Domain t :=
λ m ν, eval' ν (m _)

-- def nbe_wf : psum (Σ' {t : type}, domain ν t) (Σ' {t : type}, term ν t) → ℕ :=
-- λ v, match v with
-- | (psum.inl x) := sizeof x.fst
-- | (psum.inr x) := sizeof x.fst
-- end

-- mutual def reify, reflect
-- with reify : Π {t : type}, domain ν t → term ν t
-- | base ν := ν
-- | (arrow t₁ t₂) f := lam (λ x, reify (f (reflect (var x))))
-- with reflect : Π {t : type}, term ν t → domain ν t
-- | base m := m
-- | (arrow t₁ t₂) f := λ x, reflect (app f (reify x))
-- using_well_founded
-- { rel_tac := λ _ _, `[exact ⟨_, measure_wf (nbe_wf ν)⟩] }

def reify_reflect : Π (t : type), (domain ν t → term ν t) × (term ν t → domain ν t)
| base := ⟨ id, id ⟩
| (arrow t₁ t₂) :=
   let r₁ := reify_reflect t₁ in
   let r₂ := reify_reflect t₂ in
   let reify (f : domain ν t₁ → domain ν t₂) := lam (λ x, r₂.1 (f (r₁.2 (var x)))) in
   let reflect (f : term ν (arrow t₁ t₂)) := λ x, r₂.2 (app f (r₁.1 x)) in
   ⟨reify, reflect⟩

def reify : Domain t → Term t :=
λ x ν, (reify_reflect ν t).1 (x ν)

def normalize : Term t → Term t :=
reify ∘ eval

#eval normalize zero
#eval normalize (App succ zero)
#eval normalize (App succ (App succ zero))
#eval normalize (App succ (App succ (App succ zero)))

def i : Term (arrow (arrow base base) (arrow base base)) :=
λ ν, lam (λ f, var f)

#eval i
#eval normalize i

instance : setoid (Term t) :=
⟨inv_image eq normalize,
 inv_image.equivalence eq normalize eq_equivalence⟩

meta def canonicity : tactic unit :=
`[ try { unfold has_equiv.equiv setoid.r inv_image }, try { reflexivity } ]

def one : Term (arrow (arrow base base) (arrow base base)) :=
λ ν, lam (λ f, lam (λ x, app (var f) (var x)))

lemma zero_eqv_zero : zero ≈ zero :=
by canonicity

lemma succ_zero_eqv_one : App succ zero ≈ one :=
by canonicity

----

variable {α : Type}

inductive mem : α → list α → Type
| here : Π {x l}, mem x (x :: l)
| there : Π {x l y}, mem x l → mem x (y :: l)
open mem

local infix ` ∈' `:50 := mem

inductive judgment₁ : list type → type → Type
| var : Π {Γ t}, t ∈' Γ → judgment₁ Γ t
| lam : Π {Γ t₁ t₂}, judgment₁ (t₁ :: Γ) t₂ → judgment₁ Γ (arrow t₁ t₂)
| app : Π {Γ t₁ t₂}, judgment₁ Γ (arrow t₁ t₂) → judgment₁ Γ t₁ → judgment₁ Γ t₂
open judgment₁

variables {Γ Γ₁ Γ₂ : list type}

def judgment₁.repr' : Π {Γ t}, judgment₁ Γ t → string
| Γ _ (var h) := repr $ Γ.length - 1 - (h.rec_on (λ _ _, 0) (λ _ _ _ _ (n : ℕ), n + 1))
| Γ _ (lam m) := "(λ" ++ repr Γ.length ++ "." ++ judgment₁.repr' m ++ ")"
| _ _ (app m₁ m₂) := "(" ++ judgment₁.repr' m₁ ++ " " ++ judgment₁.repr' m₂ ++ ")"

def judgment₁.repr : Π {Γ t}, judgment₁ Γ t → string :=
λ Γ t m,
let env := (Γ.foldr (λ t p, prod.mk (prod.mk p.2 t :: p.1) (p.2 + 1)) (prod.mk [] 0)).1 in
let assigns := list.map (λ p, repr (prod.fst p) ++ " : " ++ repr (prod.snd p)) env in
string.intercalate ", " assigns ++ " ⊢ " ++ judgment₁.repr' m ++ " : " ++ repr t

instance : has_to_string (judgment₁ Γ t) :=
⟨judgment₁.repr⟩

-- x₁ : ι → ι, x₀ : ι ⊢ λ y, x₀ : (ι → ι) → ι
def ex1 : judgment₁ [arrow base base, base] (arrow (arrow base base) base) :=
lam (var (there (there here)))

#eval ex1 -- "1 : (ι → ι), 0 : ι ⊢ (λ2.0) : ((ι → ι) → ι)"

----

inductive perm : list α → list α → Type -- proof relevant version
| nil   : perm [] []
| skip  : Π {x : α} {l₁ l₂ : list α}, perm l₁ l₂ → perm (x :: l₁) (x :: l₂)
| swap  : Π {x y : α} {l : list α}, perm (y :: x :: l) (x :: y :: l)
| trans : Π {l₁ l₂ l₃ : list α}, perm l₁ l₂ → perm l₂ l₃ → perm l₁ l₃

local infix ~ := perm

def mem_perm {t : α} : Π {Γ₁ Γ₂}, Γ₁ ~ Γ₂ → t ∈' Γ₁ → t ∈' Γ₂
| _ _ perm.nil h := h
| _ _ (perm.skip _) here := here
| _ _ (perm.skip p) (there h) := there (mem_perm p h)
| _ _ perm.swap here := there here
| _ _ perm.swap (there here) := here
| _ _ perm.swap (there (there h)) := there (there h)
| _ _ (perm.trans p₁ p₂) h := mem_perm p₂ (mem_perm p₁ h)

namespace judgment₁

def xchg : Π {Γ₁ Γ₂ t}, (Γ₁ ~ Γ₂) → judgment₁ Γ₁ t → judgment₁ Γ₂ t
| _ _ _ p (var h) := var (mem_perm p h)
| _ _ _ p (lam m) := lam (xchg (perm.skip p) m)
| _ _ _ p (app m₁ m₂) := app (xchg p m₁) (xchg p m₂)

def weak : Π {Γ t₁ t₂}, judgment₁ Γ t₁ → judgment₁ (t₂ :: Γ) t₁
| _ _ _ (var h) := var (there h)
| _ _ _ (lam m) := lam (xchg perm.swap (weak m))
| _ _ _ (app m₁ m₂) := app (weak m₁) (weak m₂)

def heightof : Π {Γ t}, judgment₁ Γ t → ℕ
| _ _ (var h) := 1
| _ _ (lam m) := 1 + heightof m
| _ _ (app m₁ m₂) := 1 + max (heightof m₁) (heightof m₂)

lemma height_xchg_eq_height {m : judgment₁ Γ₁ t} : Π {Γ₂} {p : Γ₁ ~ Γ₂}, heightof (xchg p m) = heightof m :=
begin
  induction m with _ _ _ _ _ _ _ ih₁ _ _ _ _ _ ih₂ ih₃,
  { intros, refl },
  { intros, unfold xchg heightof, rw ih₁ },
  { intros, unfold xchg heightof, rw [ih₂, ih₃] }
end

def subst : Π {Γ t₁ t₂}, judgment₁ (t₁ :: Γ) t₂ → judgment₁ Γ t₁ → judgment₁ Γ t₂
| _ _ _ (var here) m := m
| _ _ _ (var (there h)) m := var h
| _ _ _ (app m₁ m₂) m :=
  have heightof m₁ < heightof (app m₁ m₂),
    by unfold heightof; rw add_comm;
    from lt_add_of_le_of_pos (le_max_left _ _) zero_lt_one,
  have heightof m₂ < heightof (app m₁ m₂),
    by unfold heightof; rw add_comm;
    from lt_add_of_le_of_pos (le_max_right _ _) zero_lt_one,
  app (subst m₁ m) (subst m₂ m)
| _ _ _ (lam m₁) m :=
  have heightof (xchg perm.swap m₁) < heightof (lam m₁),
    by unfold heightof; rw height_xchg_eq_height;
    from lt_add_of_pos_of_le zero_lt_one (le_refl _),
  lam (subst (xchg perm.swap m₁) (weak m))
using_well_founded
{ rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ v, heightof v.snd.snd.snd.fst)⟩] }

def contr : judgment₁ (t₁ :: t₁ :: Γ) t₂ → judgment₁ (t₁ :: Γ) t₂ :=
λ m, subst m (var here)

def abs : judgment₁ (t₁ :: Γ) t₂ → judgment₁ Γ (arrow t₁ t₂) :=
lam

def antiabs : judgment₁ Γ (arrow t₁ t₂) → judgment₁ (t₁ :: Γ) t₂ :=
λ m, app (weak m) (var here)

end judgment₁

---- 

def type.foldl : list type → type → type :=
λ Γ t, list.foldl (λ r t, arrow t r) t Γ

#eval type.foldl [arrow base base, base] base -- "(ι → ((ι → ι) → ι))"

namespace judgment₁

inductive env : list type → Type
| nil {} : env []
| step : Π {t Γ}, ν t → env Γ →  env (t :: Γ)

def to_term_var : Π {Γ t}, t ∈' Γ → env ν Γ → term ν t
| (_ :: Γ) _ here (env.step x _) := term.var x
| (_ :: Γ) _ (there h) (env.step _ Δ) := to_term_var h Δ

def to_term' : Π {Γ t}, judgment₁ Γ t → env ν Γ → term ν t
| _ _ (var h) Δ := to_term_var ν h Δ
| _ _ (lam m) Δ := term.lam (λ x, to_term' m (env.step x Δ))
| _ _ (app m₁ m₂) Δ := term.app (to_term' m₁ Δ) (to_term' m₂ Δ)

def foldl : Π {Γ t}, judgment₁ Γ t → judgment₁ [] (type.foldl Γ t)
| [] _ m := m
| (t :: Γ) _ m := foldl (lam m)

def to_term : judgment₁ Γ t → Term (type.foldl Γ t) :=
λ m ν, to_term' ν (foldl m) env.nil

end judgment₁

----

variables {ν₁ ν₂ : type → Type}

inductive wf : list (Σ t, ν₁ t × ν₂ t) → Π {t}, term ν₁ t → term ν₂ t → Type
| var : Π {Γ t} {x₁ : ν₁ t} {x₂ : ν₂ t}, sigma.mk t (prod.mk x₁ x₂) ∈' Γ → wf Γ (var x₁) (var x₂)
| lam : Π {Γ t₁ t₂} {f₁ : ν₁ t₁ → term ν₁ t₂} {f₂ : ν₂ t₁ → term ν₂ t₂}, (Π x₁ x₂, wf (⟨t₁, x₁, x₂⟩ :: Γ) (f₁ x₁) (f₂ x₂)) → wf Γ (lam f₁) (lam f₂)
| app : Π {Γ t₁ t₂} {m₁ : term ν₁ (arrow t₁ t₂)} {m₂ : term ν₂ (arrow t₁ t₂)} {n₁ : term ν₁ t₁} {n₂ : term ν₂ t₁}, wf Γ m₁ m₂ → wf Γ n₁ n₂ → wf Γ (app m₁ n₁) (app m₂ n₂)

def WF (t : type) (m : Term t) : Type 1 :=
Π ν₁ ν₂, wf [] (m ν₁) (m ν₂)

constant term_wf : Π t m, WF t m

def to_judgment₁_var : Π {Γ t} {x₁ : ν₁ t} {x₂ : ν₂ t}, (sigma.mk t (prod.mk x₁ x₂)) ∈' Γ → t ∈' (list.map (λ x, sigma.fst x) Γ)
| _ _ _ _ here := here
| _ _ _ _ (there h) := there (to_judgment₁_var h)

def to_judgment₁' : Π {Γ t} {m₁ : term (λ x, unit) t} {m₂ : term (λ x, unit) t}, wf Γ m₁ m₂ → judgment₁ (list.map (λ x, sigma.fst x) Γ) t
| _ _ _ _ (wf.var h) := var (to_judgment₁_var h)
| _ _ _ _ (wf.lam f) := lam (to_judgment₁' (f () ()))
| _ _ _ _ (wf.app m₁ m₂) := app (to_judgment₁' m₁) (to_judgment₁' m₂)

noncomputable def to_judgment₁ : Term t → judgment₁ [] t := 
λ m, to_judgment₁' (term_wf _ m _ _)

--------------

-- def judgment0 (t : type) := Π ν, term ν t
-- def judgment1 (t₁ t₂ : type) := Π ν, ν t₁ → term ν t₂ -- term with one free variable

def judgment₂ : list type → type → Type :=
λ Γ t, list.foldr (λ t α, ν t → α) (term ν t) Γ

def Judgment₂ (Γ : list type) (t : type) : Type 1 := -- Type 1
Π ν, judgment₂ ν Γ t

#reduce Judgment₂ [] base           -- Π ν, term ν base
#reduce Judgment₂ [base] base       -- Π ν, ν base → term ν base
#reduce Judgment₂ [base, base] base -- Π ν, ν base → ν base → term ν base
#reduce Judgment₂ [base, arrow base base] base -- Π ν, ν base → ν (arrow base base) → term ν base

def judgment₂.repr' : Π {Γ}, judgment₂ (λ t, ℕ) Γ t → ℕ → string
| [] m lv := "⊢ " ++ term.repr' m lv
| (t :: Γ) f lv := "(" ++ repr lv ++ " : " ++ repr t ++ ") " ++ judgment₂.repr' (f lv) (lv + 1)

def judgment₂.repr : Judgment₂ Γ t → string :=
λ m, judgment₂.repr' (m _) 0 ++ " : " ++ repr t

instance Judgment₂_has_repr : has_repr (Judgment₂ Γ t) :=
⟨judgment₂.repr⟩

-- x₁ : ι → ι, x₂ : ι ⊢ (λ y : ι, x₂) : ι → ι
def ex2 : Judgment₂ [arrow base base, base] (arrow base base) :=
λ ν, λ x₁ x₂, lam (λ y, var x₂)

#eval ex2 -- "(0 : (ι → ι)) (1 : ι) ⊢ (λ2.1) : (ι → ι)"

-----

def subst' : Π {t}, term (term ν) t → term ν t
| _ (var m) := m
| _ (lam f) := lam (λ x, subst' (f (var x)))
| _ (app m₁ m₂) := app (subst' m₁) (subst' m₂)

namespace judgment₂

def weak : Judgment₂ Γ t₂ → Judgment₂ (t₁ :: Γ) t₂ :=
λ m ν x, m ν

def xchg' : Π {Γ₁ Γ₂}, (Γ₁ ~ Γ₂) → judgment₂ ν Γ₁ t → judgment₂ ν Γ₂ t
| _ _ perm.nil m := m
| _ _ (perm.skip h) m := λ x, xchg' h (m x)
| _ _ perm.swap m := λ x₁ x₂, m x₂ x₁
| _ _ (perm.trans h₁ h₂) m := xchg' h₂ (xchg' h₁ m)

def xchg : (Γ₁ ~ Γ₂) → Judgment₂ Γ₁ t → Judgment₂ Γ₂ t :=
λ h m ν, xchg' ν h (m ν)

def subst'' : Π {Γ}, judgment₂ (term ν) (t₁ :: Γ) t₂ → judgment₂ ν Γ t₁ → judgment₂ ν Γ t₂
| [] m₁ m₂ := subst' ν (m₁ m₂)
| (t :: Γ) f m := λ x, subst'' (λ x', f x' (var x)) (m x)

def subst : Judgment₂ (t₁ :: Γ) t₂ → Judgment₂ Γ t₁ → Judgment₂ Γ t₂ :=
λ m₁ m₂ ν, subst'' ν (m₁ _) (m₂ ν)

def lam' : Π {Γ}, judgment₂ ν (t₁ :: Γ) t₂ → judgment₂ ν Γ (arrow t₁ t₂)
| [] m := lam (λ x, m x)
| (t :: Γ) f := λ x, lam' (λ y, f y x)

def lam : Judgment₂ (t₁ :: Γ) t₂ → Judgment₂ Γ (arrow t₁ t₂) :=
λ m ν, lam' ν (m ν)

def app' : Π {Γ}, judgment₂ ν Γ (arrow t₁ t₂) → judgment₂ ν Γ t₁ → judgment₂ ν Γ t₂
| [] m₁ m₂ := app m₁ m₂
| (t :: Γ) f m := λ x, app' (f x) (m x)

def app : Judgment₂ Γ (arrow t₁ t₂) → Judgment₂ Γ t₁ → Judgment₂ Γ t₂ :=
λ m₁ m₂ ν, app' ν (m₁ ν) (m₂ ν)

def var' : Π {Γ}, judgment₂ ν (t :: Γ) t
| [] := λ x, var x
| (t :: Γ) := λ x y, var' x

def var : Π {Γ}, t ∈' Γ → Judgment₂ Γ t
| _ here := λ ν, var' ν
| _ (there h) := weak (var h)

def contr : Judgment₂ (t₁ :: t₁ :: Γ) t₂ → Judgment₂ (t₁ :: Γ) t₂ := -- same as judgment₁.contr
λ m, subst m (var here)

def nonfree (m : Judgment₂ (t₁ :: Γ) t₂) : Prop :=
∃ m', m = weak m' -- ∃ m', ∀ ν, (λ x, (m ν) x) = (λ x, (m' ν))

-- lemma nonfree_var_lem (m : Judgment₂ (t₁ :: Γ) t₂)
-- : nonfree m ↔ ∃ (m' : Judgment₂ Γ t₂), ∀ ν, (λ x, (m ν) x) = (λ x, (m' ν)) :=
-- begin
--   unfold nonfree,
--   split,
--   { intro h,
--     induction h,
--     existsi h_w,
--     intro ν,
--     rw h_h,
--     refl },
--   { intro h,
--     induction h,
--     existsi h_w,
--     apply funext h_h }
-- end

end judgment₂

---- 

def to_term : Judgment₂ [] t → Term t :=
id

def to_judgment₂ : Term t → Judgment₂ [] t :=
id

def type.foldr : list type → type → type :=
λ Γ t, list.foldr arrow t Γ

namespace judgment₂

def abs' : Π {Γ}, judgment₂ ν Γ t → judgment₂ ν [] (type.foldr Γ t)
| [] m := m
| (t :: Γ) f := term.lam (λ x, abs' (f x))

def abs : Judgment₂ Γ t → Term (type.foldr Γ t) :=
λ m ν, abs' ν (m ν)

def antiabs' : Π {Γ}, judgment₂ (term ν) [] (type.foldr Γ t) → judgment₂ ν Γ t
| [] m := subst' ν m
| (t :: Γ) m :=
  match m with
  | (term.var x) := λ x, antiabs' (term.app m (term.var (term.var x)))
  | (term.lam f) := λ x, antiabs' (f (term.var x))
  | (term.app m₁ m₂) := λ x, antiabs' (term.app m (term.var (term.var x)))
  end

def antiabs : Judgment₂ [] (type.foldr Γ t) → Judgment₂ Γ t :=
λ m ν, antiabs' ν (m _)

end judgment₂

instance Judgment₂.setoid : setoid (Judgment₂ Γ t) :=
⟨inv_image eq (normalize ∘ to_term ∘ judgment₂.abs),
 inv_image.equivalence eq (normalize ∘ to_term ∘ judgment₂.abs) eq_equivalence⟩

def zero' : Judgment₂ [] (arrow (arrow base base) (arrow base base)) :=
(judgment₂.antiabs ∘ to_judgment₂) zero

def one' : Judgment₂ [] (arrow (arrow base base) (arrow base base)) :=
(judgment₂.antiabs ∘ to_judgment₂) one

def succ' : Judgment₂ [] (arrow (arrow (arrow base base) (arrow base base)) (arrow (arrow base base) (arrow base base))) :=
(judgment₂.antiabs ∘ to_judgment₂) succ

lemma zero_approx_zero : zero' ≈ zero' :=
by canonicity

lemma succ_zero_approx_one : judgment₂.app succ' zero' ≈ one' :=
by canonicity

end stlc