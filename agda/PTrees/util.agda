open import Data.Nat
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Binary.Core using (_≡_; refl)
  import Data.Nat.Properties
  open Data.Nat.Properties.SemiringSolver
    using (prove; solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)

module util where

Type = Set

max : ℕ → ℕ → ℕ
max 0 b = b
max b 0 = b
max (suc a) (suc b) = suc(max a b)

maxRefl : ∀{a : ℕ} → max a a ≡ a
maxRefl {0} = refl
maxRefl {suc a} rewrite maxRefl {a} = refl

power : ℕ → ℕ → ℕ
power 0       x = 1
power 1       x = x
power (suc n) x = power n x * x

-- An eaiser to read syntax.
_^_ : ℕ → ℕ → ℕ
a ^ b = power b a

factor2 : (a : ℕ) → a + a ≡ a * 2
factor2 = solve 1 (λ a → a :+ a := a :* con 2) (λ {x} → refl)

plus-0-right : ∀(n2 : ℕ) → n2 + 0 ≡ n2
plus-0-right = solve 1 (λ n2 → n2 :+ con 0 := n2) (λ {x} → refl)

unfoldPower : ∀{a b} → b ^ (suc a) ≡ (b ^ a) * b
unfoldPower {0}     {0}      = refl
unfoldPower {0}     {suc a}  rewrite plus-0-right a = refl
unfoldPower {suc a} {0}      = refl
unfoldPower {suc a} {suc b}  = refl

power2>0 : ∀{a} → ∃ λ b → 2 ^ a ≡ suc b
power2>0 {0} = 0 , refl
power2>0 {suc a} rewrite unfoldPower {a}{2} with power2>0 {a}
... | (a' , p) rewrite p = suc (a' * 2) , refl
