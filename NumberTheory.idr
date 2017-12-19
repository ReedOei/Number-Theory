module NumberTheory

import Data.So

data BothNotZero : Nat -> Nat -> Type where
  Zerophobia : BothNotZero (S n) (S m)

data Divides : Nat -> Nat -> Nat -> Type where
  DoesDivide : {a, b, c : Nat}-> (a = b*c) -> Divides a b c

data QuotRem : Nat -> Nat -> Type where
  IsQuotRem : (a, b, q, r : Nat) -> Not (b = Z) -> a = b * q + r -> LTE r (S b) -> QuotRem a b

zIsIdLeft : (n : Nat) -> n = plus 0 n
zIsIdLeft n = sym Refl

zIsIdRight : (n : Nat) -> n = plus n 0
zIsIdRight Z = Refl
zIsIdRight (S n) = eqSucc n (plus n 0) (zIsIdRight n)


mutual
  lemma : (k : Nat) -> (j : Nat) -> k + S j = j + S k
  lemma k j = trans (trans (addSIsS k j) (eqSucc (k + j) (j + k) (additionCommutes k j))) (sym (addSIsS j k))

  additionCommutesLemma : (k : Nat) -> (j : Nat) -> S (plus k (S j)) = S (plus j (S k))
  additionCommutesLemma k j = eqSucc (k + S j) (j + S k) (lemma k j)

  additionCommutes : (a, b : Nat) -> a + b = b + a
  additionCommutes Z Z = Refl
  additionCommutes Z (S k) = zIsIdRight (S k)
  additionCommutes (S k) Z = sym $ zIsIdRight (S k)
  additionCommutes (S k) (S j) = additionCommutesLemma k j

  total
  additionAssociates : (a, b, c : Nat) -> a + (b + c) = (a + b) + c
  additionAssociates Z b c = Refl
  additionAssociates (S a) b c = let recursive = additionAssociates a b c in
                                     eqSucc (a + (b + c)) ((a + b) + c) recursive

  addSIsS: (a : Nat) -> (b : Nat) -> a + S b = S (a + b)
  addSIsS Z b = Refl
  addSIsS (S k) b = eqSucc (k + S b) (S (k + b)) (addSIsS k b)

  -- addSIsS : (a, b : Nat) -> a + S b = S (a + b)
  -- addSIsS a b = let associate = additionAssociates a b 1 -- Prove a + (b + 1) = (a + b) + 1
  --                   commute = additionCommutes (a + b) 1 -- Transform (a + b) + 1 to 1 + (a + b)
  --                   associateCommute = additionAssociates 1 a b -- Transform 1 + (a + b) = (1 + a) + b
  --                   finalAssociate = additionEqRight (1 + a) (a + 1) b (additionCommutes 1 a) in -- Transform (1 + a) + b to (a + 1) + b
  --                   trans associate (trans commute associateCommute) -- Link everything together

  additionCancelsLeft : (a, b, c : Nat) -> a + b = a + c -> b = c
  additionCancelsLeft Z b c prf = prf
  additionCancelsLeft (S a) b c prf = additionCancelsLeft a b c (succInjective (a + b) (a + c) prf)

  additionCancelsRight : (a, b, c : Nat) -> b + a = c + a -> b = c
  additionCancelsRight a b c prf = let flipCPlusA = sym (additionCommutesEq c a (b + a) (sym prf)) -- Transform from b + a = c + a to b + a = a + c
                                       flipBPlusA = additionCommutesEq b a (a + c) flipCPlusA in -- Transform from b + a = a + c to a + b = a + c
                                       additionCancelsLeft a b c flipBPlusA

  additionEqLeft : (a, b, c : Nat) -> a = b -> c + a = c + b
  additionEqLeft a b Z prf = prf
  additionEqLeft a b (S c) prf = eqSucc (c + a) (c + b) (additionEqLeft a b c prf)

  additionEqRight : (a, b, c : Nat) -> a = b -> a + c = b + c
  additionEqRight a b c prf = let leftAdd = additionEqLeft a b c prf -- Prove c + a = c + b
                                  flipCPlusA = additionCommutesEq c a (c + b) leftAdd in -- Transform from c + a = c + b to a + c = c + b
                                  sym (additionCommutesEq c b (a + c) (sym flipCPlusA)) -- Transform from a + c = c + b to a + c = b + c

  additionCommutesEq : (a, b, c : Nat) -> a + b = c -> b + a = c
  additionCommutesEq a b c prf = trans (additionCommutes b a) prf

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

