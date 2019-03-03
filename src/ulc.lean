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

def preterm.repr' : preterm ℕ → ℕ → string
| (var n) _ := repr n
| (lam f) lv := "(λ" ++ repr lv ++ "." ++ preterm.repr' (f lv) (lv + 1) ++ ")"
| (app m₁ m₂) lv := "(" ++ preterm.repr' m₁ lv ++ " " ++ preterm.repr' m₂ lv ++ ")"

def preterm.repr (m : Preterm) : string :=
preterm.repr' (m ℕ) 0

instance Preterm_has_repr : has_repr Preterm :=
⟨preterm.repr⟩

def i : Preterm := λ α, lam (λ x, var x)
#eval i
--> (λ0.0)

def s : Preterm := λ α, lam (λ x, lam (λ y, lam (λ z, app (app (var x) (var z)) (app (var y) (var z)))))
def k : Preterm := λ α, lam (λ x, lam (λ y, var x))
#eval s
--> (λ0.(λ1.(λ2.((0 2) (1 2)))))
#eval k
--> (λ0.(λ1.0))

def n₀ : Preterm := λ α, lam (λ f, lam (λ x, var x))
def n₁ : Preterm := λ α, lam (λ f, lam (λ x, app (var f) (var x)))
def n₂ : Preterm := λ α, lam (λ f, lam (λ x, app (var f) (app (var f) (var x))))
def n₃ : Preterm := λ α, lam (λ f, lam (λ x, app (var f) (app (var f) (app (var f) (var x)))))

#eval n₀
--> (λ0.(λ1.1))
#eval n₁
--> (λ0.(λ1.(0 1)))
#eval n₂
--> (λ0.(λ1.(0 (0 1))))
#eval n₃
--> (λ0.(λ1.(0 (0 (0 1)))))

def succ : Preterm := λ α, lam (λ n, lam (λ f, lam (λ x, app (var f) (app (app (var n) (var f)) (var x)))))

def App : Preterm → Preterm → Preterm :=
λ m₁ m₂ α, app (m₁ α) (m₂ α)

def succ_n₀ : Preterm := App succ n₀

#eval succ_n₀
--> ((λ0.(λ1.(λ2.(1 ((0 1) 2))))) (λ0.(λ1.1)))

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

#eval succ_n₀
--> ((λ0.(λ1.(λ2.(1 ((0 1) 2))))) (λ0.(λ1.1)))
#eval pbeta succ_n₀
--> (λ0.(λ1.(0 (((λ2.(λ3.3)) 0) 1))))
#eval pbeta (pbeta succ_n₀)
--> (λ0.(λ1.(0 ((λ2.2) 1))))
#eval pbeta (pbeta (pbeta succ_n₀))
--> (λ0.(λ1.(0 1)))
#eval pbeta (pbeta (pbeta (pbeta succ_n₀)))
--> (λ0.(λ1.(0 1)))

def ω : Preterm := λ α, lam (λ x, app (var x) (var x))
def Ω : Preterm := App ω ω

#eval Ω
--> ((λ0.(0 0)) (λ0.(0 0)))
#eval pbeta Ω
--> ((λ0.(0 0)) (λ0.(0 0)))

-- def isapp : Preterm₀ → Preterm₀
-- | (lam f) := f
-- | (app m₁ m₂) := t