import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic

section test1

universe u v

#check Nat × Bool
def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2

#check Type 0
/-
f has four arguments
1 = Type
2 = (fun α => α)
3 = Nat
4 = x

α = Type 0: Type 1

β = (fun α => α) : Type 0 → Type 0
because the template says the domain is
α, and we know that α = Type 0, and the function
is an identity, so the codomain is also Type 0.

a = Nat : Type 0, which is consistent with the template's requirement that a has type α

β a = a = Nat : Type 0

so b = x : Nat, which is consistent with the template's requirement that b has type β a = Nat



-/

end test1

section test2
universe u
def ident {α : Type u} (x : α) := x
#check (ident)
end test2

#check List
#check [2]
