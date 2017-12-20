module NumberTheory

import Data.So

data BothNotZero : Nat -> Nat -> Type where
  Zerophobia : BothNotZero (S n) (S m)

data Divides : Nat -> Nat -> Type where
  DoesDivide : (a, b, n : Nat) -> (b = n*a) -> Divides a b

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
  -- addSIsS a b = let addOne = additionEqLeft (1 + b) (b + 1) a (additionCommutes 1 b) -- Prove a + (1 + b) = a + (b + 1)
  --                   associate = additionAssociates a b 1 -- Prove a + (b + 1) = (a + b) + 1
  --                   commute = additionCommutes (a + b) 1 -- Transform (a + b) + 1 to 1 + (a + b)
  --                   associateCommute = additionAssociates 1 a b in -- Transform 1 + (a + b) = (1 + a) + b
  --                   trans (trans (trans addOne associate) commute) associateCommute -- Link everything together

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

minusZIsZ : (a : Nat) -> {auto smaller : LTE 0 a} -> a = a - 0
minusZIsZ Z = Refl
minusZIsZ (S k) = Refl

addMinusCancel : (a, b : Nat) -> LTE b a -> a = a - b + b
addMinusCancel a Z prf =
      -- Get the expression a + 0 = a - 0 + 0
  let prepareProp = additionEqRight a (a - 0) Z (minusZIsZ a) in
      trans (zIsIdRight a) prepareProp

zMultIsZRight : (a : Nat) -> 0 = mult a 0
zMultIsZRight Z = Refl
zMultIsZRight (S a) = zMultIsZRight a

lteSuccInjective : (a, b : Nat) -> LTE (S a) (S b) -> LTE a b
lteSuccInjective _ _ LTEZero impossible
lteSuccInjective _ _ (LTESucc prf) = prf

checkLTE : (a, b : Nat) -> Dec (LTE a b)
checkLTE Z b = Yes LTEZero
checkLTE (S a) Z = No succNotLTEzero
checkLTE (S a) (S b) =
  case checkLTE a b of
       Yes prfLTE => Yes (LTESucc prfLTE)
       No prfGT   => No (\prf => prfGT (lteSuccInjective a b prf))

divides : (a, b : Nat) -> Dec (Divides a b)
divides a Z = Yes (DoesDivide a Z Z Refl)
divides a b =
  case checkLTE a b of
      Yes prfLTE => case divides a (b - a) of
                         -- This is a proof that b - a = n * a
                         -- Therefore, we can show that b = S n * a
                                                           -- Prove that b = b - a + a
                         Yes (DoesDivide _ _ n prf) => let bId = addMinusCancel b a prfLTE
                                                           -- Prove that (b - a) + a = a + (b - a)
                                                           aCommute = additionCommutes (b - a) a
                                                           -- Prove that a + (b - a) = a + (n * a)
                                                           sNWorks = additionEqLeft (b - a) (n * a) a prf in
                                                           -- Link everything together, using the definition of mult to prove
                                                           -- a + n * a = S n * a
                                                           -- Then we get b = S n * a, Q.E.D.
                                                           Yes (DoesDivide a b (S n) (trans (trans (trans bId aCommute) sNWorks) Refl))
                         No prf => No ?nohole2
      No prfGT  => ?nohole

