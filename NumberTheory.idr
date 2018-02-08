import NumberTheory.NatThms

data Divides : Nat -> Nat -> Type where
  DoesDivide : (a, b, n : Nat) -> (b = n*a) -> Divides a b

data Mod : Nat -> Nat -> Nat -> Type where
  Congruent : (a, b, n : Nat) -> Divides n (minus b a) -> Mod a b n

data GCD : Nat -> Nat -> Nat -> Type where
  GCDAZero : (b : Nat) -> GCD Z b b
  GCDEq : (a, b, x, y, n : Nat) -> Divides n a -> Divides n b -> a*x + b*y = n -> GCD a b n

data ZZ : Nat -> Nat -> Type where
  Zero : ZZ 0 0
  Positive : (a : Nat) -> ZZ a 0
  Negative : (b : Nat) -> ZZ 0 b

dividesRefl : Divides a a
dividesRefl = DoesDivide a a 1 (multOneIsIdLeft a)

anyDividesZ : Divides a 0
anyDividesZ = DoesDivide a Z Z Refl

dividesTrans : (a, b, c : Nat) -> Divides a b -> Divides b c -> Divides a c
dividesTrans a b c (DoesDivide _ _ n prf) (DoesDivide _ _ m prf2) =
  let -- m*b = m*(n*a)
      step1 = multEqLeft b (n*a) m prf
      -- m*(n*a) = (m*n)*a
      step2 = multAssociates m n a in
      -- Becase c = m*b, c = (m*n)*a
      DoesDivide a c (m*n) (trans (trans prf2 step1) step2)

dividesMult : (a, b, c : Nat) -> Divides a b -> Divides a (b*c)
dividesMult a b c (DoesDivide _ _ n prf) = let step1 = multCommutes b c
                                               step2 = trans (multEqLeft b (n*a) c prf) (multAssociates c n a) in
                                               DoesDivide a (b*c) (c*n) (trans step1 step2)

dividesABC : (a, b, c : Nat) -> Divides a (b*c) -> Either (Divides a b) (Divides a c)
dividesABC a b c (DoesDivide _ _ n prf) = ?dividesABC_rhs

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

