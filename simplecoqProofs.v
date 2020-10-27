Theorem left_and_elimination : forall X Y : Prop, (and X Y) -> X.

Proof.

intros.
destruct H.
assumption.
Show Proof.

Qed.

Theorem left_and_elimination_2 : forall X Y : Prop, (and X Y) -> X.

Proof.

exact (fun X Y and_data => (proj1 and_data)).

Qed.







Require Import Arith.


Goal forall X Y : Prop, X -> Y -> X.

Proof.
intros.
assumption.
Qed.

Goal forall X Y : Prop, X -> Y -> X.

(** intros X Y A B 
gives us A of type X and B of type Y,
then we just return A **)

Proof.
  intros X Y A B. exact A.
Qed.

Goal forall X : Prop, X -> X.
Proof.
  intros X. exact (fun A : X => A).
Qed.

(** 
(fun A : X => Q).
means lambda (A:X).Q

**)

Goal forall X Y : Prop, X -> Y -> X.

(** intros X Y A B 
gives us A of type X and B of type Y,
then we just return A **)

Proof.
  intros X Y. exact (fun A B => A).
Qed.

Goal forall X Y : Prop, X -> Y -> X.


Proof.
  exact (fun X Y A B => A).
Qed.

(** above is shorthand for **)

Goal forall X Y : Prop, X -> Y -> X.


Proof.
  exact (fun X : Prop => fun Y : Prop => fun A : X => fun B : Y => A).
Qed.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Eval compute in (minustwo 4).


Goal forall X Y Z : Prop, (X -> Y) -> (Y -> Z) -> (X -> Z).

Proof. 
  exact (fun X Y Z f g v => (g (f v))).
Qed.

(** 
https://coq.inria.fr/library/Coq.Init.Logic.html
**)


Goal forall X Y : Prop, (and X Y) -> X.

Proof.
  exact (fun X Y k => (proj1 k)).
Qed.

(** modus tollens **)
Goal forall X Y : Prop, (X -> Y) -> (not Y) -> (X -> False).

Proof.
  Definition m : (forall X Y : Prop, (X -> Y) -> (not Y) -> (X -> False)) := fun X Y imp Yto0 xval => (Yto0 (imp xval)).
  exact (m).
Qed.

(** inductive definitions, disjunction, 
forall, exists, pi type, sigma type, 
LST, HoTT, proof general, number theory etc. 
**)

Goal 41 + 1 = 42.

Proof.
reflexivity.
Show Proof.
Qed.

Check eq_refl.

Check (7 = 7).


Goal exists n:nat, n + 1 = 42.

Proof.
  apply ex_intro with (x:=41).
   reflexivity.
Show Proof.
Qed.

(** if there exists a proof x of A such that P(x) then A is true **)

(** Goal forall R : Prop -> Prop, ((exists V : Prop, (R V)) -> ). 
Proof.
  exact (fun R v => 
**)

(**

Goal forall (A:Type), (forall R : A -> Prop, ( ((exists a : A, True)) -> ((forall a : A, R a)) -> (exists a : A, R a))).

Proof.
exact (fun A R elem forallfn => (Yto0 (imp xval))).
   reflexivity.
Qed.

**)

(** forall n, n + 2 == n + 1 **)

(** forall X -> X -> exists X

sigma and pi types

inductive definitions

LST

hott

**)

Definition add7 (n : nat) : nat := n + 7.

Eval compute in (add7 4).


Fixpoint times7 (n : nat) : nat := 
 match n with
    | O => O
    | S n' => (times7 n') + 7
  end.

Eval compute in (times7 4).

Require Import List.

Check 1::2::3::nil.


(** 

Inductive or (A B:Prop) : Prop :=
  | or_introl : A -> A \/ B
  | or_intror : B -> A \/ B

**)


Goal forall X Y Z : Prop, (X -> Z) -> (Y -> Z) -> ((or X Y) -> Z).

Proof.
  Definition peicewise : (forall X Y Z : Prop, (X -> Z) -> (Y -> Z) -> ((or X Y) -> Z)) := fun X Y Z f g n =>
  match n with
    | (or_introl x) => (f x)
    | (or_intror y) => (g y)
  end.
  exact (peicewise).
Qed.

Theorem modusPonens (p : Prop) (q : Prop) :
  (and p (p -> q)) -> q.
Proof.
exact (fun data => (proj2 data) (proj1 data)).
Qed.

Theorem modusPonens2 (p : Prop) (q : Prop) :
  (and p (p -> q)) -> q.
Proof.
intros.
destruct H.
exact (H0 H).
Qed.

Theorem modusPonens3 (p : Prop) (q : Prop) :
  (and p (p -> q)) -> q.
Proof.
intros.
destruct H.
apply H0 in H as newthing.
assumption.
Qed.

Theorem modusPonens4 (p : Prop) (q : Prop) :
  (and p (p -> q)) -> q.
Proof.
exact (modusPonens3 p q).
Qed.

Theorem ex_falso_quodlibet : forall (X : Prop), False -> X.
Proof.
  intros X contra.
  inversion contra.
Show Proof.
Qed.

(** the above defines our void function **)




Theorem onlyone : forall P Q : Prop, (and (or P Q) (P -> False)) -> Q.
Proof.
  intros.
  destruct H.
  Definition f : (forall P Q : Prop, P \/ Q -> (P -> False) -> Q) := fun P Q orish H0 =>
  match orish with
    | (or_introl x) => (ex_falso_quodlibet Q (H0 x))
    | (or_intror y) => y
  end.
  exact (f P Q H H0).
Show Proof.
Qed.

Theorem anything_implies_true : forall P : Prop, (P -> True).
Proof.
  exact (fun P x => I).
Qed.


Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Check conj.

Theorem producty_pair : forall X Y H : Prop, (H -> X) -> (H -> Y) -> (H -> (and X Y)).

Proof.
exact ( fun X Y H f g h => (conj (f h) (g h))).
Show Proof.
Qed.

 

Inductive my_nat : Type := 
  | Zero
  | Suc (n : my_nat).


(**
Theorem frobenius (A : Set) (p : A -> Prop) (q : Prop) :
  (exists x : A, q /\ p x) <-> (q /\ exists x :A, p x).
Proof.
**)

Theorem and_implies : forall X Y H : Prop, (X -> H) -> ((and X Y) -> H).

Proof.
exact ( fun X Y H f p => f (proj1 p)).
Qed.


Definition addThem (n: nat) (m: nat) : nat := n + m.

Fixpoint addThem2 (n: nat) (m: nat) : nat := 
  match m with 
    | 0 => n
    | S m' => S (addThem2 n m')
  end.

Eval compute in (addThem2 4 7).




