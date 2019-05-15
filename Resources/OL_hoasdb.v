(****************************************************************
   File: OL_hoasdb.v
   Authors: Chelsea Battell
   Version: Coq V8.5
   Date: July 2016

   Encoding of the syntax of a logic mapping between HOAS and
   De Bruijn representations of lambda-terms, following the paper
   "Reasoning About Higher-Order Relational Specifications" by Wang
   et al.
  ***************************************************************)

Require Import Hybrid.

Section hoas_db.

Inductive Econ : Set :=
| hAPP : Econ
| hABS : Econ
| dAPP : Econ
| dABS : Econ
| dVAR : nat -> Econ.

Definition tm : Set := expr Econ.
Definition dtm : Set := expr Econ.

Definition hApp : tm -> tm -> tm :=
 fun (e1 : tm) =>
  fun (e2 : tm) =>
   APP (APP (CON hAPP) e1) e2.
Definition hAbs : (tm -> tm) -> tm :=
 fun (f : tm -> tm) =>
  APP (CON hABS) (lambda f).

Definition dApp : dtm -> dtm -> dtm :=
 fun (d1 : dtm) =>
  fun (d2 : dtm) =>
   APP (APP (CON dAPP) d1) d2.
Definition dAbs : dtm -> dtm :=
 fun (d : dtm) =>
  APP (CON dABS) d.
Definition dVar : var -> dtm :=
 fun (v : var) =>
  (CON (dVAR v)).

End hoas_db.

Require Import Hsl_submission.

Section encoding.

Inductive atm : Set :=
| hodb : tm -> nat -> dtm -> atm.

Definition X : Set := nat.

Definition oo_ := oo atm Econ X.
Definition atom_ : atm -> oo_ := atom Econ X.
Definition T_ : oo_ := T atm Econ X.

Definition context_ := context atm Econ X.
Definition empty_con_ : context_ := Empty_set oo_.

Hint Unfold oo_ atom_ T_ context_ empty_con_: hybrid.

(****************************************************************
   Definition of prog
  ****************************************************************)

Notation "a & b" := (Conj a b) (at level 60, right associativity). 
Notation "a ---> b" := (Imp a b) (at level 61, right associativity).
Notation "<< a >>" := (atom_ a) (at level 30).

Inductive prog : atm -> oo_ -> Prop :=
| hodb_app : forall (e1 e2 : tm) (n : nat) (d1 d2 : dtm),
   prog (hodb (hApp e1 e2) n (dApp d1 d2))
    ((<<hodb e1 n d1>>) & (<<hodb e2 n d2>>))
| hodb_abs : forall (f : tm -> tm) (n : nat) (d : dtm),
   abstr f ->
   prog (hodb (hAbs f) n (dAbs d))
    (All (fun (x : tm) =>
     (Allx (fun (k : X) => (<<hodb x (n + k) (dVar k)>>))) --->
      (<<hodb (f x) (n + 1) d>>))).

(****************************************************************
   Instantiation of seq and bch
  ****************************************************************)

Definition grseq_ : context_ -> oo_ -> Prop := grseq prog.
Definition grseq0 (B : oo_) : Prop := grseq_ empty_con_ B.

Definition bcseq_ : context_ -> oo_ -> atm -> Prop := bcseq prog.

(*Notation "a :- b" := (prog a b) (at level 60).

Notation "{ L |- G }" := (seq prog L G).
Notation "{ |- G }" := (seq0 G).
Notation "{ |- G }" := (seq prog empty_con_ G).
Notation "{ L , [ F ] |- A }" := (bch prog L F A).
Notation "{ [ F ] |- A }" := (bch prog empty_con_ F A).*)

Theorem hodb_det1 :
 forall (L : context_) (e1 e2 : tm) (d : dtm) (n : nat),
  grseq_ L (<<hodb e1 n d>>) ->
  grseq_ L (<<hodb e2 n d>>) ->
  e1 = e2.
Proof.
Admitted.

Theorem hodb_det3 :
 forall (L : context_) (e : tm) (d1 d2 : dtm) (n : nat),
  grseq_ L (<<hodb e n d1>>) ->
  grseq_ L (<<hodb e n d2>>) ->
  d1 = d2.
Proof.
Admitted.

End encoding.