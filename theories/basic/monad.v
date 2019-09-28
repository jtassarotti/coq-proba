From discprob.basic Require Import base.

(** Some basic type classes/notation for monadic operations from
    coq-stdpp which is BSD licensed; see opam listing for details *)

(* Note: the type classes don't actually stipulate that the appropriate laws hold *)

From stdpp Require Import base.

Definition mbind := @stdpp.base.mbind.
Definition mjoin := @stdpp.base.mjoin.
Definition fmap := @stdpp.base.fmap.
Definition mret := @stdpp.base.mret.
Arguments mbind {_ _ _ _} _ _ /.
Arguments fmap {_ _ _ _} _ _ /.
Arguments mjoin {_ _ _} _ /.
Arguments mret {_ _ _} _ /.
Notation MBind := stdpp.base.MBind.
Notation MRet := stdpp.base.MRet.
Notation MJoin := stdpp.base.MJoin.
Notation FMap := stdpp.base.FMap.
Global Open Scope stdpp_scope. 
Notation "m ≫= f" := (mbind f m) (at level 60, right associativity) : stdpp_scope.
Notation "( m ≫=)" := (λ f, mbind f m) (only parsing) : stdpp_scope.
Notation "(≫= f )" := (mbind f) (only parsing) : stdpp_scope.
Notation "(≫=)" := (λ m f, mbind f m) (only parsing) : stdpp_scope.

Notation "x ← y ; z" := (y ≫= (λ x : _, z))
  (at level 20, y at level 100, z at level 200, only parsing) : stdpp_scope.
Infix "<$>" := fmap (at level 61, left associativity) : stdpp_scope.
Notation "' ( x1 , x2 ) ← y ; z" :=
  (y ≫= (λ x : _, let ' (x1, x2) := x in z))
  (at level 65, right associativity) : stdpp_scope.
Notation "' ( x1 , x2 , x3 ) ← y ; z" :=
  (y ≫= (λ x : _, let ' (x1,x2,x3) := x in z))
  (at level 65, only parsing, right associativity) : stdpp_scope.
Notation "' ( x1 , x2 , x3  , x4 ) ← y ; z" :=
  (y ≫= (λ x : _, let ' (x1,x2,x3,x4) := x in z))
  (at level 65, only parsing, right associativity) : stdpp_scope.
Notation "' ( x1 , x2 , x3  , x4 , x5 ) ← y ; z" :=
  (y ≫= (λ x : _, let ' (x1,x2,x3,x4,x5) := x in z))
  (at level 65, only parsing, right associativity) : stdpp_scope.
Notation "' ( x1 , x2 , x3  , x4 , x5 , x6 ) ← y ; z" :=
  (y ≫= (λ x : _, let ' (x1,x2,x3,x4,x5,x6) := x in z))
  (at level 65, only parsing, right associativity) : stdpp_scope.