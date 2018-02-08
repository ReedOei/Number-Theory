module ZThms

import NumberTheory.NatThms

%default total
%access public export

data ZZ : Nat -> Nat -> Type where
  Zero : ZZ 0 0
  Positive : (a : Nat) -> ZZ a 0
  Negative : (b : Nat) -> ZZ 0 b

