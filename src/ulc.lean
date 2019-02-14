-- 1. untyped lambda calculus

-- inductive preterm : Type
-- | lam : (preterm → preterm) → preterm
-- | app : preterm → preterm → preterm

inductive preterm (α : Type) : Type
| var : α → preterm
| lam : (α → preterm) → preterm
| app : preterm → preterm → preterm
open preterm

def Preterm : Type 1 := -- Type 1
Π α, preterm α

def preterm.to_string : preterm ℕ → ℕ → string
| (var n) _ := to_string n
| (lam f) lv := "(λ" ++ to_string lv ++ "." ++ preterm.to_string (f lv) (lv + 1) ++ ")"
| (app m₁ m₂) lv := "(" ++ preterm.to_string m₁ lv ++ " " ++ preterm.to_string m₂ lv ++ ")"

def Preterm.to_string (m : Preterm) : string :=
preterm.to_string (m ℕ) 0

instance : has_to_string Preterm :=
⟨Preterm.to_string⟩

def i : Preterm := λ α, lam (λ x, var x)
#eval to_string i -- "(λ0.0)"
def s : Preterm := λ α, lam (λ x, lam (λ y, lam (λ z, app (app (var x) (var z)) (app (var y) (var z)))))
#eval to_string s -- "(λ0.(λ1.(λ2.((0 2) (1 2)))))"
def k : Preterm := λ α, lam (λ x, lam (λ y, var x))
#eval to_string k -- "(λ0.(λ1.0))"

def n₀ : Preterm := λ α, lam (λ f, lam (λ x, var x))
#eval to_string n₀  -- "(λ0.(λ1.1))"
def n₁ : Preterm := λ α, lam (λ f, lam (λ x, app (var f) (var x)))
#eval to_string n₁  -- "(λ0.(λ1.(0 1)))"
def n₂ : Preterm := λ α, lam (λ f, lam (λ x, app (var f) (app (var f) (var x))))
#eval to_string n₂  -- "(λ0.(λ1.(0 (0 1))))"
def n₃ : Preterm := λ α, lam (λ f, lam (λ x, app (var f) (app (var f) (app (var f) (var x)))))
#eval to_string n₃  -- "(λ0.(λ1.(0 (0 (0 1)))))"

def succ : Preterm := λ α, lam (λ n, lam (λ f, lam (λ x, app (var f) (app (app (var n) (var f)) (var x)))))
#eval to_string succ -- "(λ0.(λ1.(λ2.(1 ((0 1) 2)))))"

def App : Preterm → Preterm → Preterm :=
λ m₁ m₂ α, app (m₁ α) (m₂ α)

def succ_n₀ : Preterm := App succ n₀
#eval to_string succ_n₀ -- "((λ0.(λ1.(λ2.(1 ((0 1) 2))))) (λ0.(λ1.1)))"

def subst' {α} : preterm (preterm α) → preterm α
| (var x) := x
| (lam f) := lam (λ x, subst' (f (var x))) -- terminates!
| (app m₁ m₂) := app (subst' m₁) (subst' m₂)

def pbeta' {α} : preterm (preterm α) → preterm α -- parallel beta
| (var x) := x
| (lam f) := lam (λ x, pbeta' (f (var x)))
| (app (lam f) m) := subst' (f (subst' m))
| (app n m) := app (pbeta' n) (pbeta' m)

def pbeta : Preterm → Preterm :=
λ m α, pbeta' (m _)

#eval to_string succ_n₀ -- "((λ0.(λ1.(λ2.(1 ((0 1) 2))))) (λ0.(λ1.1)))"
#eval to_string $ pbeta succ_n₀ -- "(λ0.(λ1.(0 (((λ2.(λ3.3)) 0) 1))))"
#eval to_string $ pbeta $ pbeta succ_n₀ -- "(λ0.(λ1.(0 ((λ2.2) 1))))"
#eval to_string $ pbeta $ pbeta $ pbeta succ_n₀ -- "(λ0.(λ1.(0 1)))"
#eval to_string $ pbeta $ pbeta $ pbeta $ succ_n₀ -- "(λ0.(λ1.(0 1)))"

def ω : Preterm := λ α, lam (λ x, app (var x) (var x))
def Ω : Preterm := App ω ω
#eval to_string Ω -- "((λ0.(0 0)) (λ0.(0 0)))"
#eval to_string $ pbeta $ Ω -- "((λ0.(0 0)) (λ0.(0 0)))"

-- def isapp : Preterm₀ → Preterm₀
-- | (lam f) := f
-- | (app m₁ m₂) := t