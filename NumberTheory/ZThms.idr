module ZThms

import NumberTheory.NatThms

%default total
%access public export

data ZZ : Type where
  Zero : ZZ
  Positive : (a : Nat) -> Not (a = 0) -> ZZ
  Negative : (b : Nat) -> Not (b = 0) -> ZZ

Num ZZ where
  -- fromInteger 0 = Zero
  -- fromInteger a = if a > 0 then
  --                   Positive (fromInteger a)
  --                 else
  --                   Negative (fromInteger (-a))

  a + Zero = a
  Zero + b = b
  (Positive a prf1) + (Positive b prf2) = ?hole -- Positive (a + b) ?hole
  -- (Negative a) + (Negative b) = Negative (a + b)
  -- (Positive a) + (Negative b) = case checkLTE b a of
  --                                    Yes prf => Positive (a - b)
  --                                    No prfNo => Zero
  -- (Negative a) + (Positive b) = case checkLTE a b of
  --                                    Yes prf => Zero
  --                                    No prfNo => Zero

