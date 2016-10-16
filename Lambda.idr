module Lambda

import Data.Vect
import Lemmas
import public Data.Fin
import public Calculus

%default total
%access export


||| The base cases of Term used to end the recursion.
public export
data BaseTerm : Type -> (ctxt : Nat) -> Type where
  ||| A abstract (free) variable which doesn't depend on the context for
  ||| interpretation. Could be anything from meta variables/placeholders
  ||| in an incomplete program to even constants. Use "Void" as the type
  ||| to only allow construction of closed terms.
  Free : a -> BaseTerm a ctxt
  ||| A normally bound variable (reference to some binder) which can be
  ||| dangling (free) if context allows.
  Ref : Fin ctxt -> BaseTerm a ctxt

||| A abstract representation of lambda calculus terms. Intended usage
||| involves using a string type for "id" if named terms are desired
||| or "()" (Unit) if nameless terms are wanted.
public export
data Term : Type -> Type -> (ctxt : Nat) -> Type where
  ||| A leaf node (usually containing bound variables) which contains data
  ||| which may depend on the context for correct interpretation.
  Leaf : BaseTerm fr ctxt -> Term id fr ctxt
  ||| A lambda abstraction containing a term with the same context + 1 more binder
  ||| in context.
  Lam : id -> Term id fr $ S ctxt -> Term id fr ctxt
  App : Term id fr ctxt -> Term id fr ctxt -> Term id fr ctxt

%name BaseTerm x, y, z
%name Term t, u, s, p, q, r
%name Fin n, m, i, j, k

||| A Term having "ctxt" = 0 ensures that there are no dangling references embedded within.
public export
ClosedBound : Type -> Type -> Type
ClosedBound id = flip (Term id) 0

||| A Term having "ctxt" = S _ ensures that the *maximum* number of dangling unique references
||| embedded within is greater than 0. There need not be any dangling references, however.
public export
OpenBound : Type -> Type -> Nat -> Type
OpenBound id fr p@(S _) = Term id fr p
OpenBound _ _ Z = Void

hasFree : Term id fr p -> Bool
hasFree (Leaf (Free _)) = True
hasFree (Leaf _) = False
hasFree (Lam _ t) = hasFree t
hasFree (App t u) = hasFree t || hasFree u

public export
data HasFree : Term id fr p -> Type where
  FreeHasFree : HasFree $ Leaf $ Free _
  LamHasFree : HasFree t -> HasFree $ Lam _ t
  AppHasFree : Either (HasFree t) (HasFree u) -> HasFree $ App t u

showImplicit : Show fr => BaseTerm fr ctxt -> String
showImplicit (Free x) = "(Free " ++ show x ++ ")"
showImplicit (Ref n) = show $ finToNat n

implementation Show fr => Show (BaseTerm fr ctxt) where
  show = showImplicit

isFree : BaseTerm fr ctxt -> Bool
isFree (Free _) = True
isFree _ = False

isRef : BaseTerm fr ctxt -> Bool
isRef (Ref _) = True
isRef _ = False

isLeaf : Term id fr p -> Bool
isLeaf (Leaf _) = True
isLeaf _ = False

isLam : Term id fr p -> Bool
isLam (Lam _ _) = True
isLam _ = False

isApp : Term id fr p -> Bool
isApp (App _ _) = True
isApp _ = False

open : (p : Nat) -> Term id fr q -> Term id fr $ p + q
open n   (Leaf (Ref m)) {q} = Leaf $ Ref $ rewrite plusCommutative n q in weakenN n m
open n t@(Leaf (Free _)) = t
open n   (Lam x t) {q} = Lam x $ rewrite plusSuccRightSucc n q in open n t
open n   (App t u) = App (open n t) (open n u)

openUntil : (p : Nat) -> Term id fr q -> Term id fr $ maximum p q
openUntil p t {q} = rewrite diffPlusIsMax p q in open (minus p q) t

matchCtxt : Term id fr p -> Term id fr q -> (Term id fr $ maximum p q, Term id fr $ maximum p q)
matchCtxt t u {p} {q} = (rewrite maximumCommutative p q in openUntil q t, openUntil p u)

free : fr -> Term id fr p
free = Leaf . Free

ref : Fin p -> Term id fr p
ref = Leaf . Ref

app : Term id fr p -> Term id fr q -> Term id fr $ maximum p q
app t u = let (t, u) = matchCtxt t u in App t u

||| If a term is an abstraction, peel off the first sequence of consecutive abstractions.
peel : ClosedBound id fr -> (p : Nat ** (Vect p id, Term id fr p))
peel t = peel' t [] where
  peel' : Term id fr p -> Vect p id -> (q : Nat ** (Vect q id, Term id fr q))
  peel' (Lam x t) xs = peel' t $ x::xs
  peel' t xs {p} = (p ** (xs, t))

||| Close over a term with as many lambda abstractions as needed to
||| bound all dangling references.
enclose : Vect p id -> Term id fr p -> ClosedBound id fr
enclose [] t@(Leaf (Free x)) = t
enclose []   (Leaf (Ref FZ)) impossible
enclose []   (Leaf (Ref (FS _))) impossible
enclose [] t@(Lam _ _) = t
enclose [] t@(App _ _) = t
enclose (x :: xs) t = enclose xs $ Lam x t

||| Determines if a Term is a "value".
isVal : Term id fr p -> Bool
isVal = isLam

||| Substitute a term s with a "closed bound" inside a term t with an "open bound" of 1
||| in place of an implicit variable n, which always equals the maximum bounded number
||| and the only dangling reference in any subterm of t, resulting in a new term with a
||| "closed bound". Unlike traditional substitution functions on lambda terms using
||| De Bruijn indices, no shifting is needed as free variables are handled seperately
||| from bound variables in the definition of lambda terms used here, but in order to
||| pass type checking the bound on s must be opened.
subst : ClosedBound id fr -> Term id fr 1 -> ClosedBound id fr
subst s t = subst' s t where
  subst' : Term id fr p -> Term id fr $ S p -> Term id fr p
  subst' s t@(Leaf (Free _)) = t
  subst' s   (Leaf (Ref m)) = case (strengthen m) of
                                  -- m could not strengthen ≡ m = last ≡ m = the variable being substituted
                                  (Left m) => s
                                  -- m could     strengthen ≡ m < last ≡ m ≠ the variable being substituted
                                  (Right m) => ref m
  subst' s   (Lam x t) = Lam x $ subst' (open 1 s) t
  subst' s   (App t u) = App (subst' s t) (subst' s u)

||| One-step call-by-value evaluation where the result specifies if termination was achieved.
reduce1ByValue : ClosedBound id fr -> Evaluation $ ClosedBound id fr
reduce1ByValue (App (Lam _ t) s@(Lam _ _)) = Reduction $ subst s t -- There can only be one variable to substitute for in this context so it is left implicit.
reduce1ByValue (App t@(Lam _ _) u@(App _ _)) = case (reduce1ByValue u) of
                                                    Reduction u' => Reduction $ App t u'
                                                    Termination nf => Termination nf
reduce1ByValue (App t@(App _ _) u) = case (reduce1ByValue t) of
                                          Reduction t' => Reduction $ App t' u
                                          Termination nf => Termination nf
reduce1ByValue t = Termination $ if isVal t then Value else Stuck

partial
implementation Calculus (ClosedBound id fr) where
    reduce1 = reduce1ByValue
    isVal = Lambda.isVal
