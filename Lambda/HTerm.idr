module Lambda.HTerm

import Language.Reflection.Utils
import Data.Vect
import public Lambda

%default total
%access export

dsl term
  variable    = ref
  index_first = FZ
  index_next  = FS
  lambda      = Lam {id = TTName}

||| A Term using higher-order variable bindings.
public export
HTermN : Type -> Nat -> Type
HTermN fr n = Term TTName fr n

||| A Term with a "closed bound" using higher-order variable bindings.
public export
HTerm : Type -> Type
HTerm = flip HTermN 0

||| An HTerm which can only be constructed without free variables.
public export
HClosed : Type
HClosed = HTerm Void

(<*>) : HTermN a p -> HTermN a p -> HTermN a p
(<*>) = App

pure : HTermN a p -> HTermN a p
pure = id

implementation Show a => Show (HTerm a) where
    show (Leaf (Ref FZ)) impossible
    show (Leaf (Ref (FS _))) impossible
    show t = show' t [] where
      show' : HTermN a p -> Vect p TTName -> String
      show' (Leaf (Free x)) env = show "Free " ++ show x
      show' (Leaf (Ref n)) env = show $ index n env
      show' (Lam x t) env {p} = "(λ" ++ show x ++ ". " ++ (show' t $ the (Vect (S p) TTName) $ x::env) ++ ")"
      show' (App t u) env = "(" ++ show' t env ++ " " ++ show' u env ++ ")"
