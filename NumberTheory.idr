module NumberTheory

import Data.So

data BothNotZero : Nat -> Nat -> Type where
  Zerophobia : BothNotZero (S n) (S m)

data Divides : Nat -> Nat -> Nat -> Type where
  DoesDivide : {a, b, c : Nat}-> (a = b*c) -> Divides a b c

data QuotRem : Nat -> Nat -> Type where
  IsQuotRem : (a, b, q, r : Nat) -> Not (b = Z) -> a = b * q + r -> LTE r (S b) -> QuotRem a b

addZeroRHS : (k : Nat) -> k = plus k 0
addZeroRHS {k = Z} = Refl
addZeroRHS {k = (S j)} = let recursive = addZeroRHS j in
                             eqSucc j (plus j 0) recursive

addSIsS: (a : Nat) -> (b : Nat) -> a + S b = S (a + b)
addSIsS Z b = Refl
addSIsS (S k) b = eqSucc (k + S b) (S (k + b)) (addSIsS k b)

mutual
  lemma : (k : Nat) -> (j : Nat) -> k + S j = j + S k
  lemma k j = trans (trans (addSIsS k j) (eqSucc (k + j) (j + k) (additionCommutes k j))) (sym (addSIsS j k))

  additionCommutesLemma : (k : Nat) -> (j : Nat) -> S (plus k (S j)) = S (plus j (S k))
  additionCommutesLemma k j = eqSucc (k + S j) (j + S k) (lemma k j)

  additionCommutes : (a, b : Nat) -> a + b = b + a
  additionCommutes {a = Z} {b = Z} = Refl
  additionCommutes {a = Z} {b = (S k)} = addZeroRHS (S k)
  additionCommutes {a = (S k)} {b = Z} = sym $ addZeroRHS (S k)
  additionCommutes (S k) (S j) = additionCommutesLemma k j

additionAssociates : (a, b, c : Nat) -> a + (b + c) = (a + b) + c

addZero : Z + a = a
addZero = Refl

multAddZero : Z = ((a * Z) + Z)
multAddZero = ?multAddZero_rhs

rIsLTB : (r : Nat) -> (b : Nat) -> (prf : Not (b = Z)) -> LTE r (S b)

total quotRem : (a : Nat) -> (b : Nat) -> Not (b = Z) -> QuotRem a b
quotRem _ Z prf = void (prf Refl)
quotRem Z b prf = IsQuotRem Z b Z Z prf multAddZero (rIsLTB Z b prf)
quotRem a b prf = ?what

-- data Congruence : Nat -> Nat -> Nat -> Type where
--   -- a = b + n*k
--   Congruent : (a : Nat) -> (b : Nat) -> (n : Nat) -> Congruence a b n
