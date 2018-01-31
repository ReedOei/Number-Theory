module NumberTheory

import Data.So

data BothNotZero : Nat -> Nat -> Type where
  Zerophobia : BothNotZero (S n) (S m)

data Divides : Nat -> Nat -> Type where
  DoesDivide : (a, b, n : Nat) -> (b = n*a) -> Divides a b

data Mod : Nat -> Nat -> Nat -> Type where
  Congruent : (a, b, n : Nat) -> Divides n (minus b a) -> Mod a b n

data GCD : Nat -> Nat -> Nat -> Type where
  GCDAZero : (b : Nat) -> GCD Z b b
  GCDEq : (a, b, x, y, n : Nat) -> Divides n a -> Divides n b -> a*x + b*y = n -> GCD a b n

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

dividesRefl : Divides a a
dividesRefl = DoesDivide a a 1 (multOneIsIdLeft a)

anyDividesZ : Divides a 0
anyDividesZ = DoesDivide a Z Z Refl

dividesTrans : (a, b, c : Nat) -> Divides a b -> Divides b c -> Divides a c
dividesTrans a b c (DoesDivide _ _ n prf) (DoesDivide _ _ m prf2) = DoesDivide a c (m*n) ?hole

dividesABC : (a, b, c : Nat) -> Divides a (b*c) -> Either (Divides a b) (Divides a c)


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
                                                           Yes (DoesDivide a (S b) (S n) (trans (trans bId aCommute) sNWorks))
                         -- a does not divides (b - a), so a cannot divide b
                         No prf => No (\contra =>
                                  case contra of
                                       -- b = a * k; k = S n
                                       -- k cannot be 0, because that implies that S b is 0, but obviously it's can't be.
                                       DoesDivide _ _ Z false => void (SIsNotZ false)

                                       -- The goal here is to prove that, if S b = (S n) * a, then S b - a = n*a
                                       -- We know this is false, (because we checked above), so this leads to a contradiction.
                                       (DoesDivide _ _ (S n) false) =>
                                              -- S b - a = a + n*a - a
                                          let sbEqualsNAInit = minusEqRight (S b) (a + n*a) a false prfLTE (partLessThanSumRight (n*a) a)
                                              -- a + n*a - a = n*a + a - a
                                              commuteAdd = minusEqRight (a + n*a) (n*a + a) a (additionCommutes a (n*a)) (partLessThanSumRight (n*a) a) (partLessThanSum (n*a) a)
                                              -- n*a + a - a = n*a
                                              nTimesA = sym (addMinusCancel (n*a) a (partLessThanSum (n*a) a))
                                              -- Combining the equalities above gives us: S b - a = n*a, as we wanted.
                                              sbEqualsNAProof = trans (trans sbEqualsNAInit commuteAdd) nTimesA
                                              aDividesSBMinusA = DoesDivide a (S b - a) n sbEqualsNAProof in
                                              prf aDividesSBMinusA)
      No prfGT  => No (\contra =>
                  case contra of
                       -- b = a * k; k = S n
                       -- k cannot be 0, because that implies that S b is 0, but obviously it can't be
                       DoesDivide _ _ Z false => void (SIsNotZ false)
                       (DoesDivide _ _ (S n) false) =>
                            -- For any a, we have a <= a + n*a
                        let aLTAPlusAN = partLessThanSumRight (n*a) a in
                            -- If a did divide S b, then we would have S b = a + n*a
                            -- As S b = a + n*a, we must have a <= a + n*a <= S b
                            -- But we know that a > S b, so we have a contradiction.
                            prfGT (replace (sym false) aLTAPlusAN))

-- euclideanAlg : (a, b : Nat) -> NotBothZero a b -> GCD a b n
-- euclideanAlg {n} Z b _ =
--   case decEq b n of
--        Yes prf => replace prf (GCDEq Z b Z 1 b anyDividesZ dividesRefl (sym (multOneIsIdRight b)))
--        No prf  => void ?hole

