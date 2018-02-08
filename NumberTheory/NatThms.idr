module NatThms

import Data.So

%default total
%access public export

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

  addEqsIsEq : (a, b, c, d : Nat) -> a = b -> c = d -> a + c = b + d
  addEqsIsEq a b c d prf prf1 = trans (additionEqRight a b c prf) (additionEqLeft c d b prf1)

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

minusEqLeft : (a, b, c : Nat) -> a = b -> LTE a c -> LTE b c -> c - a = c - b
minusEqLeft (S _) (S _) Z _ _ _ impossible
minusEqLeft Z Z _ _ _ _ = Refl
minusEqLeft Z (S _) _ prf _ _ = void (SIsNotZ (sym prf))
minusEqLeft (S _) Z _ prf _ _ = void (SIsNotZ prf)
minusEqLeft (S a) (S b) (S c) prf prfLTEac prfLTEbc = minusEqLeft a b c (succInjective a b prf) (lteSuccInjective a c prfLTEac) (lteSuccInjective b c prfLTEbc)

predEq : (a, b : Nat) -> a = b -> Nat.pred a = Nat.pred b
predEq  Z Z prf = Refl
predEq  Z (S _) prf = void (SIsNotZ (sym prf))
predEq  (S _) Z prf = void (SIsNotZ prf)
predEq  (S a) (S b) prf = succInjective a b prf

ltePredLHS : (a, b : Nat) -> LTE (S a) b -> LTE a b
ltePredLHS Z Z prf = void (succNotLTEzero prf)
ltePredLHS Z (S b) (LTESucc _) = LTEZero
ltePredLHS (S a) (S b) (LTESucc prf) = LTESucc (ltePredLHS a b prf)

lteSuccRHS : (a, b : Nat) -> LTE a b -> LTE a (S b)
lteSuccRHS Z _ _ = LTEZero
lteSuccRHS (S _) Z _ impossible
lteSuccRHS (S a) (S b) prf = LTESucc (lteSuccRHS a b (lteSuccInjective a b prf))

minusSuccIsPred : (a, b : Nat) -> minus a (S b) = pred (minus a b)
minusSuccIsPred Z _ = Refl
minusSuccIsPred (S a) Z = sym (minusZIsId a)
minusSuccIsPred (S a) (S b) = minusSuccIsPred a b

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

partLessThanSum : (a, b : Nat) -> LTE b (a + b)
partLessThanSum _ Z = LTEZero
partLessThanSum Z (S b) = lteRefl
partLessThanSum (S a) (S b) = let recursive = LTESucc (partLessThanSum a b)
                                  -- Show that S b < S (a + b) implies S b < a + S b using addSIsS
                                  addSIsSLTE = replace (sym (addSIsS a b)) recursive in
                                  lteSuccRHS (S b) (a + S b) addSIsSLTE

partLessThanSumRight : (a, b : Nat) -> LTE b (b + a)
partLessThanSumRight a b = replace (additionCommutes a b) (partLessThanSum a b)

minusAddSIsS : (a, b : Nat) -> minus (S (a + b)) (S b) = minus (a + S b) (S b)
minusAddSIsS a b = let test2 = partLessThanSum a (S b)
                       test3 = replace (addSIsS a b) test2 in
                       minusEqRight (S (a + b)) (a + S b) (S b) (sym (addSIsS a b)) test3 test2

aMinusAIsZ : (a : Nat) -> minus a a = 0
aMinusAIsZ Z = Refl
aMinusAIsZ (S k) = aMinusAIsZ k

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
minusAddCancel Z Z LTEZero = Refl
minusAddCancel (S k) b prf =
  case decEq (S k) b of
       Yes prfEq   => let step1_1 = trans (minusEqRight (S k) b b prfEq prf lteRefl) (aMinusAIsZ b)
                          step1 = additionEqRight (S k - b) 0 b step1_1 in
                          sym (trans step1 (sym prfEq))
       No prfNotEq => let recursive = minusAddCancel k b in
                          ?hole2
-- minusAddCancel a (S k) prf = let recursive = minusAddCancel a k (ltePredLHS k a prf) in
--                                  ?hole

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

multEqLeft : (a, b, c : Nat) -> a = b -> c * a = c * b
multEqLeft a b Z prf = Refl
multEqLeft a b (S k) prf = let recursive = multEqLeft a b k prf in
                               addEqsIsEq a b (k*a) (k*b) prf recursive

multOneIsIdLeft : (a : Nat) -> a = 1 * a
multOneIsIdLeft Z = Refl
multOneIsIdLeft (S a) = eqSucc a (1 * a) (multOneIsIdLeft a)

multOneIsIdRight : (a : Nat) -> a = a * 1
multOneIsIdRight Z = Refl
multOneIsIdRight (S a) = eqSucc a (a * 1) (multOneIsIdRight a)

distribute : (a, b, c : Nat) -> a * (b + c) = a * b + a * c
distribute Z b c = Refl
distribute (S k) b c = let -- k*(b+c) = k*b+k*c
                           recursive = distribute k b c
                           -- (b+c) + (k*(b+c)) = (b+c) + (k*b+k*c)
                           step1 = additionEqLeft (k*(b+c)) (k*b+k*c) (b+c) recursive
                           -- (b+c) + (k*b+k*c) = b + (c + (k*b+k*c))
                           step2 = sym (additionAssociates b c (k*b+k*c))
                           -- b + (c + (k*b+k*c)) = b + ((k*b+k*c)+c)
                           step3 = additionEqLeft (c+(k*b+k*c)) ((k*b+k*c)+c) b (additionCommutes c (k*b+k*c))
                           -- b + ((k*b+k*c)+c) = b + (k*b+(k*c+c))
                           step4 = sym (additionEqLeft (k*b+(k*c+c)) ((k*b+k*c)+c) b (additionAssociates (k*b) (k*c) c))
                           -- k*b + (c+k*c) = k*b + (k*c+c)
                           step5_1 = additionEqLeft (c+k*c) (k*c+c) (k*b) (additionCommutes c (k*c))
                           -- b + (k*b+(k*c+c)) = b + (k*b+(c+k*c))
                           step5 = sym (additionEqLeft (k*b+(c+k*c)) (k*b+(k*c+c)) b step5_1)
                           -- b + (k*b+(c+k*c)) = (b+k*b)+(c+k*c)
                           step6 = additionAssociates b (k*b) (c + k*c) in
                           -- Connect everything
                           trans (trans (trans (trans (trans step1 step2) step3) step4) step5) step6

multCommutes : (a, b : Nat) -> a * b = b * a
multCommutes Z b = zMultIsZRight b
multCommutes (S k) b = let -- k*b = b*k
                           recursive = multCommutes k b
                           -- b*(1 + k) = b*1 + b*k
                           step1 = distribute b 1 k
                           -- b*1 + b*k = b + b*k
                           step2 = additionEqRight (b * 1) b (b*k) (sym (multOneIsIdRight b))
                           -- b + b*k = b + k*b
                           step3 = sym (additionEqLeft (k*b) (b*k) b recursive) in
                           sym (trans (trans step1 step2) step3)

multAssociates : (a, b, c : Nat) -> a * (b * c) = (a * b) * c
multAssociates Z b c = Refl
multAssociates (S k) b c = let -- k*(b*c) = (k*b)*c
                               recursive = multAssociates k b c
                               -- k*(b*c) = c*(k*b)
                               step1_1 = trans recursive (multCommutes (k*b) c)
                               -- b*c + k*(b*c) = b*c + c*(k*b)
                               step1 = additionEqLeft (k*(b*c)) (c*(k*b)) (b*c) step1_1
                               -- b*c + c*(k*b) = c*b + c*(k*b)
                               step2 = additionEqRight (b*c) (c*b) (c*(k*b)) (multCommutes b c)
                               -- c*b + c*(k*b) = c*(b+k*b)
                               step3 = sym (distribute c b (k*b))
                               -- c*(b+b*k) = (b+b*k)*c
                               step4 = multCommutes c (b+k*b) in
                               trans step1 (trans step2 (trans step3 step4))

