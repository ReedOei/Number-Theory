import NumberTheory.NatThms
import NumberTheory.Divides

data Mod : Nat -> Nat -> Nat -> Type where
  Congruent : (a, b, n : Nat) -> Divides n (minus b a) -> Mod a b n

data GCD : Nat -> Nat -> Nat -> Type where
  GCDAZero : (b : Nat) -> GCD Z b b
  GCDEq : (a, b, x, y, n : Nat) -> Divides n a -> Divides n b -> a*x + b*y = n -> GCD a b n

data ZZ : Nat -> Nat -> Type where
  Zero : ZZ 0 0
  Positive : (a : Nat) -> ZZ a 0
  Negative : (b : Nat) -> ZZ 0 b

-- euclideanAlg : (a, b : Nat) -> NotBothZero a b -> GCD a b n
-- euclideanAlg {n} Z b _ =
--   case decEq b n of
--        Yes prf => replace prf (GCDEq Z b Z 1 b anyDividesZ dividesRefl (sym (multOneIsIdRight b)))
--        No prf  => void ?hole

