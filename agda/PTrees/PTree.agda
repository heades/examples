open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import util

module PTree where

data PTree : (h : ℕ) -> Type where
  leaf : (el : ℕ) -> PTree 0
  node : (h : ℕ) -> (key : ℕ) 
                 -> (ltree : PTree h)                     
                 -> (rtree : PTree h) 
                 -> PTree (1 + h)

a : ℕ
a = 1
b : ℕ
b = 2
c : ℕ
c = 3
d : ℕ
d = 4

exPTree : PTree 2 
exPTree = 
    node 1 1
         (node 0 3
               (leaf a) 
               (leaf b)) 
         (node 0 2
               (leaf c) 
               (leaf d))

internalHeight : ∀{h : ℕ} → PTree h → ℕ
internalHeight (leaf _) = 0
internalHeight (node h' _ _ _) = 1 + h'

interHParaEq : ∀{h : ℕ}{tr1 tr2 : PTree h} → internalHeight tr1 ≡ internalHeight tr2
interHParaEq {0}{leaf _}{leaf _} = refl
interHParaEq {suc a}{node .a _ _ _}{node .a _ _ _} = refl

interHEq : ∀{h : ℕ}{tr : PTree h} → internalHeight tr ≡ h
interHEq {0}{leaf _} = refl
interHEq {suc a}{node .a _ _ _} = refl

externalHeight : ∀{h : ℕ} → PTree h → ℕ
externalHeight (leaf _) = 0
externalHeight (node h _ ltree rtree) = 1 + (max (externalHeight ltree) (externalHeight rtree))

heightCorrect : ∀{h : ℕ}{tr : PTree h} → externalHeight tr ≡ internalHeight tr
heightCorrect {0}{leaf _} = refl
heightCorrect {suc a}{node .a _ ltree rtree} with (externalHeight ltree) | heightCorrect {tr = ltree}
... | ._ | refl with externalHeight rtree | heightCorrect {tr = rtree} 
... | ._ | refl with internalHeight ltree | interHParaEq {tr1 = ltree}{tr2 = rtree}
... | ._ | refl with internalHeight rtree | interHEq {tr = rtree} 
... | ._ | refl rewrite maxRefl {a} = refl

numNodes : ∀{h : ℕ} → PTree h → ℕ
numNodes {0} (leaf _) = 1
numNodes {suc a} (node .a _ ltr rtr) = 1 + (numNodes ltr) + (numNodes rtr)

numNodesArith : ∀{a} → suc ((2 ^ (suc a) ∸ 1) + (2 ^ (suc a) ∸ 1)) ≡ (2 ^ (suc a) * 2) ∸ 1
numNodesArith {a} with power2>0 {suc a} 
... | (a' , p') with power (suc a) 2 | p' 
... | ._ | refl rewrite factor2 a' = refl 

numNodesCorrect : ∀{h : ℕ}{tr : PTree h} → numNodes tr ≡ 2 ^ (1 + h) ∸ 1
numNodesCorrect {0}{leaf _} = refl
numNodesCorrect {suc a}{node .a _ ltr rtr} with numNodes ltr |  numNodesCorrect {tr = ltr}
... | ._ | refl  rewrite numNodesCorrect {tr = rtr} = numNodesArith {a}
