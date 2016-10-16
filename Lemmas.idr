||| Miscellaneous proofs, most of which were only relevant for brief moments during hacking
||| and which are saved for later just in case.
module Lemmas

import Data.Fin

%access public export
%default total

lastIsNotLT : (p : Fin $ S k) -> compare (Fin.last {n = k}) p = LT -> Void
lastIsNotLT {k = Z} FZ Refl impossible
lastIsNotLT {k = Z} (FS FZ) _ impossible
lastIsNotLT {k = Z} (FS (FS _)) _ impossible
lastIsNotLT {k = S _} FZ Refl impossible
lastIsNotLT {k = S k} (FS n) prf with (compare last n) proof prf'
  lastIsNotLT {k = S k} (FS n) Refl | LT = lastIsNotLT n $ sym prf'

lastIsGTE : (p : Fin $ S k) -> compare (Fin.last {n = k}) p = o -> Either (o = GT) (o = EQ)
lastIsGTE p prf with (compare last p) proof prf'
  lastIsGTE p _   | LT = absurd $ lastIsNotLT p $ sym prf'
  lastIsGTE p prf | GT = Left $ sym prf
  lastIsGTE p prf | EQ = Right $ sym prf


firstIsLast : (p : Fin 1) -> p = Fin.last
firstIsLast FZ = Refl
firstIsLast (FS FZ) impossible
firstIsLast (FS (FS _)) impossible

lastIsFirst : (p = Fin.last {n = 0}) -> FZ = p
lastIsFirst Refl = Refl

succIsLast : p = Fin.last {n = m} -> FS p = Fin.last {n = S m}
succIsLast Refl = Refl

firstStrengthens : (p : Fin $ S k) -> (prf : p = FZ) -> compare p Fin.last = LT -> (q : Fin k ** strengthen p = Right q)
firstStrengthens {k = Z} FZ Refl Refl impossible
firstStrengthens {k = (S k)} FZ Refl Refl = (FZ ** Refl)
firstStrengthens {k = (S _)} (FS _) Refl _ impossible

cmpEq : (p : Nat) -> (q : Nat) -> {auto prf : compare p q = EQ} -> p = q
cmpEq Z Z = Refl
cmpEq Z (S _) {prf = Refl} impossible
cmpEq (S _) Z {prf = Refl} impossible
cmpEq (S m) (S n) {prf} = rewrite (cmpEq m n {prf = prf}) in Refl

maxEq : (p : Nat) -> (q : Nat) -> {auto prf : compare p q = EQ} -> maximum p q = p
maxEq Z Z = Refl
maxEq Z (S _) {prf = Refl} impossible
maxEq (S _) Z {prf = Refl} impossible
maxEq (S m) (S n) {prf} = rewrite maxEq m n {prf=prf} in Refl

diffPlusIsMax : (p : Nat) -> (q : Nat) -> maximum p q = ((minus p q) + q)
diffPlusIsMax Z n = Refl
diffPlusIsMax m Z = rewrite minusZeroRight m in
                       rewrite plusZeroRightNeutral m in
                       rewrite maximumZeroNLeft m in Refl
diffPlusIsMax (S m) (S n) = rewrite sym $ plusSuccRightSucc (minus m n) n in
                               rewrite diffPlusIsMax m n in Refl
