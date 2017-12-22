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

minusZIsId : (a : Nat) -> {auto smaller : LTE 0 a} -> a = a - 0
minusZIsId Z = Refl
minusZIsId (S k) = Refl

lteSuccInjective : (a, b : Nat) -> LTE (S a) (S b) -> LTE a b
lteSuccInjective _ _ LTEZero impossible
lteSuccInjective _ _ (LTESucc prf) = prf

total
minusEqLeft : (a, b, c : Nat) -> a = b -> LTE a c -> LTE b c -> c - a = c - b
minusEqLeft (S _) (S _) Z _ _ _ impossible
minusEqLeft Z Z _ _ _ _ = Refl
minusEqLeft Z (S _) _ prf _ _ = void (SIsNotZ (sym prf))
minusEqLeft (S _) Z _ prf _ _ = void (SIsNotZ prf)
minusEqLeft (S a) (S b) (S c) prf prfLTEac prfLTEbc = minusEqLeft a b c (succInjective a b prf) (lteSuccInjective a c prfLTEac) (lteSuccInjective b c prfLTEbc)

total
predEq : (a, b : Nat) -> a = b -> Nat.pred a = Nat.pred b
predEq  Z Z prf = Refl
predEq  Z (S _) prf = void (SIsNotZ (sym prf))
predEq  (S _) Z prf = void (SIsNotZ prf)
predEq  (S a) (S b) prf = succInjective a b prf

total
ltePredLHS : (a, b : Nat) -> LTE (S a) b -> LTE a b
ltePredLHS Z Z prf = void (succNotLTEzero prf)
ltePredLHS Z (S b) (LTESucc _) = LTEZero
ltePredLHS (S a) (S b) (LTESucc prf) = LTESucc (ltePredLHS a b prf)

total
lteSuccRHS : (a, b : Nat) -> LTE a b -> LTE a (S b)
lteSuccRHS Z _ _ = LTEZero
lteSuccRHS (S _) Z _ impossible
lteSuccRHS (S a) (S b) prf = LTESucc (lteSuccRHS a b (lteSuccInjective a b prf))

total
minusSuccIsPred : (a, b : Nat) -> minus a (S b) = pred (minus a b)
minusSuccIsPred Z _ = Refl
minusSuccIsPred (S a) Z = sym (minusZIsId a)
minusSuccIsPred (S a) (S b) = minusSuccIsPred a b

total
minusEqRight : (a, b, c : Nat) -> a = b -> LTE c a -> LTE c b -> a - c = b - c
minusEqRight Z Z Z _ _ _ = Refl
minusEqRight Z (S _) _ prf _ _ = void (SIsNotZ (sym prf))
minusEqRight (S _) Z _ prf _ _ = void (SIsNotZ prf)
minusEqRight a b Z prf _ _ = trans (trans (sym (minusZIsId a)) prf) (minusZIsId b)
minusEqRight a b (S c) prf prfLTE1 prfLTE2 =
      -- Get a proof that a - c = b - c
  let recursive = minusEqRight a b c prf (ltePredLHS c a prfLTE1) (ltePredLHS c b prfLTE2)
      -- Show that pred (a - c) = pred (b - c)
      predAreEq = predEq (minus a c) (minus b c) recursive
      -- Transform a - S c = pred (a - c) into a - S c = pred (b - c)
      aPredIsBPred = trans (minusSuccIsPred a c) predAreEq in
      -- Finish by showing that a - S c = pred (a - c) = pred (b - c) = b - S c
      trans aPredIsBPred (sym (minusSuccIsPred b c))

total
testAA : (a, b, c : Nat) -> LTE (S (b + c)) a -> LTE (b + S c) a -> a - S (b + c) = a - (b + S c)
testAA a b c prf1 prf2 = minusEqLeft (S (b + c)) (b + S c) a (sym (addSIsS b c)) prf1 prf2

total
testAB : (a, b : Nat) -> LTE b a -> a - b = S a - S b
testAB a b prf = Refl

total
partLessThanSum : (a, b : Nat) -> LTE b (a + b)
partLessThanSum _ Z = LTEZero
partLessThanSum Z (S b) = lteRefl
partLessThanSum (S a) (S b) = let recursive = LTESucc (partLessThanSum a b)
                                  -- Show that S b < S (a + b) implies S b < a + S b using addSIsS
                                  addSIsSLTE = replace (sym (addSIsS a b)) recursive in
                                  lteSuccRHS (S b) (a + S b) addSIsSLTE

total
partLessThanSumRight : (a, b : Nat) -> LTE b (b + a)
partLessThanSumRight a b = replace (additionCommutes a b) (partLessThanSum a b)

minusAddSIsS : (a, b : Nat) -> minus (S (a + b)) (S b) = minus (a + S b) (S b)
minusAddSIsS a b = let test2 = partLessThanSum a (S b)
                       test3 = replace (addSIsS a b) test2 in
                       minusEqRight (S (a + b)) (a + S b) (S b) (sym (addSIsS a b)) test3 test2

total
addMinusCancel : (a, b : Nat) -> LTE b (a + b) -> a = (a + b) - b
addMinusCancel Z Z _ = Refl
addMinusCancel a Z _ = trans (zIsIdRight a) (minusZIsId (a + 0))
addMinusCancel a (S b) prf =
  let recursive = addMinusCancel a b (partLessThanSum a b) in
      trans recursive (minusAddSIsS a b)

minusAddCancel : (a, b : Nat) -> LTE b a -> a = a - b + b
minusAddCancel a Z prf =
      -- Get the expression a + 0 = a - 0 + 0
  let prepareProp = additionEqRight a (a - 0) Z (minusZIsId a) in
      trans (zIsIdRight a) prepareProp

zMultIsZRight : (a : Nat) -> 0 = mult a 0
zMultIsZRight Z = Refl
zMultIsZRight (S a) = zMultIsZRight a

checkLTE : (a, b : Nat) -> Dec (LTE a b)
checkLTE Z b = Yes LTEZero
checkLTE (S a) Z = No succNotLTEzero
checkLTE (S a) (S b) =
  case checkLTE a b of
       Yes prfLTE => Yes (LTESucc prfLTE)
       No prfGT   => No (\prf => prfGT (lteSuccInjective a b prf))

divides : (a, b : Nat) -> Dec (Divides a b)
divides a Z = Yes (DoesDivide a Z Z Refl)
divides a (S b) =
  case checkLTE a (S b) of
      Yes prfLTE => case divides a ((S b) - a) of
                         -- This is a proof that b - a = n * a
                         -- Therefore, we can show that b = S n * a
                                                           -- Prove that b = b - a + a
                         Yes (DoesDivide _ _ n prf) => let bId = minusAddCancel (S b) a prfLTE
                                                           -- Prove that (b - a) + a = a + (b - a)
                                                           aCommute = additionCommutes (S b - a) a
                                                           -- Prove that a + (b - a) = a + (n * a)
                                                           sNWorks = additionEqLeft (S b - a) (n * a) a prf in
                                                           -- Link everything together, using the definition of mult to prove
                                                           -- a + n * a = S n * a
                                                           -- Then we get b = S n * a, Q.E.D.
                                                           Yes (DoesDivide a (S b) (S n) (trans (trans (trans bId aCommute) sNWorks) Refl))
                         -- a does not divides (b - a), so a cannot divide b
                         No prf => No (\(DoesDivide _ _ (S n) false) =>
                                  let test = minusEqRight (S b) (a + n*a) a false prfLTE (lteAddRight a {m=n*a})
                                      test2 = additionCommutes a (n*a)
                                      test25 = trans false test2
                                      test3 = sym (addMinusCancel (n*a) a (partLessThanSum (n*a) a))
                                      test6 = minusEqRight (a + n*a) (n*a + a) a test2 (partLessThanSumRight (n*a) a) (partLessThanSum (n*a) a)
                                      test7 = trans (trans test test6) test3
                                      test4 = DoesDivide a (S b - a) n test7 in
                                      prf test4)
      No prfGT  => No (\lamp =>
                  case lamp of
                       DoesDivide _ _ Z false => void (SIsNotZ false)
                       (DoesDivide _ _ (S n) false) =>
                            -- For any a, we have a <= a + n*a
                        let aLTAPlusAN = partLessThanSumRight (n*a) a in
                            -- If a did divide S b, then we would have S b = a + n*a
                            -- As S b = a + n*a, we must have a <= a + n*a <= S b
                            -- But we know that a > S b, so we have a contradiction.
                            prfGT (replace (sym false) aLTAPlusAN))

