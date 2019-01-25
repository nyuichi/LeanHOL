-- 1. untyped lambda calculus

-- inductive preterm₀ : Type
-- | lam : (preterm₀ → preterm₀) → preterm₀
-- | app : preterm₀ → preterm₀ → preterm₀

inductive preterm₁ (α : Type) : Type
| var : α → preterm₁
| lam : (α → preterm₁) → preterm₁
| app : preterm₁ → preterm₁ → preterm₁
open preterm₁

def Preterm₁ : Type 1 := -- Type 1
Π α, preterm₁ α

def preterm₁.to_string : preterm₁ ℕ → ℕ → string
| (var n) _ := to_string n
| (lam f) lv := "(λ" ++ to_string lv ++ "." ++ preterm₁.to_string (f lv) (lv + 1) ++ ")"
| (app m₁ m₂) lv := "(" ++ preterm₁.to_string m₁ lv ++ " " ++ preterm₁.to_string m₂ lv ++ ")"

def Preterm₁.to_string (m : Preterm₁) : string :=
preterm₁.to_string (m ℕ) 0

instance : has_to_string Preterm₁ :=
⟨Preterm₁.to_string⟩

def i : Preterm₁ := λ α, lam (λ x, var x)
#eval to_string i -- "(λ0.0)"
def s : Preterm₁ := λ α, lam (λ x, lam (λ y, lam (λ z, app (app (var x) (var z)) (app (var y) (var z)))))
#eval to_string s -- "(λ0.(λ1.(λ2.((0 2) (1 2)))))"
def k : Preterm₁ := λ α, lam (λ x, lam (λ y, var x))
#eval to_string k -- "(λ0.(λ1.0))"

def n₀ : Preterm₁ := λ α, lam (λ f, lam (λ x, var x))
#eval to_string n₀  -- "(λ0.(λ1.1))"
def n₁ : Preterm₁ := λ α, lam (λ f, lam (λ x, app (var f) (var x)))
#eval to_string n₁  -- "(λ0.(λ1.(0 1)))"
def n₂ : Preterm₁ := λ α, lam (λ f, lam (λ x, app (var f) (app (var f) (var x))))
#eval to_string n₂  -- "(λ0.(λ1.(0 (0 1))))"
def n₃ : Preterm₁ := λ α, lam (λ f, lam (λ x, app (var f) (app (var f) (app (var f) (var x)))))
#eval to_string n₃  -- "(λ0.(λ1.(0 (0 (0 1)))))"

def succ : Preterm₁ := λ α, lam (λ n, lam (λ f, lam (λ x, app (var f) (app (app (var n) (var f)) (var x)))))
#eval to_string succ -- "(λ0.(λ1.(λ2.(1 ((0 1) 2)))))"
def succ_n₀ : Preterm₁ := λ α, app (succ α) (n₀ α)
#eval to_string succ_n₀ -- "((λ0.(λ1.(λ2.(1 ((0 1) 2))))) (λ0.(λ1.1)))"

def subst' {α} : preterm₁ (preterm₁ α) → preterm₁ α
| (var x) := x
| (lam f) := lam (λ x, subst' (f (var x))) -- terminates!
| (app m₁ m₂) := app (subst' m₁) (subst' m₂)

def pbeta' {α} : preterm₁ (preterm₁ α) → preterm₁ α -- parallel beta
| (var x) := x
| (lam f) := lam (λ x, pbeta' (f (var x)))
| (app (lam f) m) := subst' (f (subst' m))
| (app n m) := app (pbeta' n) (pbeta' m)

def pbeta : Preterm₁ → Preterm₁ :=
λ m α, pbeta' (m _)

#eval to_string succ_n₀ -- "((λ0.(λ1.(λ2.(1 ((0 1) 2))))) (λ0.(λ1.1)))"
#eval to_string $ pbeta succ_n₀ -- "(λ0.(λ1.(0 (((λ2.(λ3.3)) 0) 1))))"
#eval to_string $ pbeta $ pbeta succ_n₀ -- "(λ0.(λ1.(0 ((λ2.2) 1))))"
#eval to_string $ pbeta $ pbeta $ pbeta succ_n₀ -- "(λ0.(λ1.(0 1)))"
#eval to_string $ pbeta $ pbeta $ pbeta $ succ_n₀ -- "(λ0.(λ1.(0 1)))"

def ω : Preterm₁ := λ α, lam (λ x, app (var x) (var x))
def Ω : Preterm₁ := λ α, app (ω α) (ω α)
#eval to_string Ω -- "((λ0.(0 0)) (λ0.(0 0)))"
#eval to_string $ pbeta $ Ω -- "((λ0.(0 0)) (λ0.(0 0)))"
