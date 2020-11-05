
(** 1 basics **)

(** examples of dependent functions **)


Definition pick_first (a : Type) (b : Type) : Type := a.

Compute pick_first nat bool. 

Definition return_7 (a : Type) (b : Type) : nat := 7.

Compute return_7 nat bool. 


(** 1a identity **)


(** Definition my_id (t : Type) : t -> t := (fun a => a). **)

Definition my_id : (forall t : Type, t -> t) := (fun t a => a).

(** 
Pi _{x : A} B(x) is (forall x : A, B(x))
fun is a constructor
evaluation is a desctructor
**)


Compute my_id nat 7.

Check my_id.


Theorem identity_1a : forall t : Type, t -> t.
Proof.
exact (my_id).
Show Proof.
Qed.

(** 1b composition **)

Definition my_composition : (forall a b c : Type, (b -> c) -> (a -> b) -> (a -> c)) 
:= (fun a b c g f av => g (f av)).


Definition add1 : nat -> nat := (fun x => x + 1).

Compute (my_composition nat nat nat add1 add1) 7.

(** 1c introducing functions **)

(** 
Pi _{x : A} B(x) is (forall x : A, B(x))
**)

Definition my_type : Type := forall x : bool, nat.
Compute my_type. 

(** 2 finite products **)

(** 2a unit type **)

Inductive my_unit : Set :=
    my_star : my_unit.

Definition type_to_unit : (forall t : Type, t -> my_unit) := (fun t a => my_star).

Compute type_to_unit nat 7.




(** WE WANT CODE TO VERIFY THE UNIQUENESS OF AN ARROW INTO THE UNIT TYPE **)

(** 2b products **)

Inductive my_prod (A B:Type) : Type :=
  my_pair : A -> B -> (my_prod A B).

Definition my_fst : (forall A B : Type, (my_prod A B) -> A) := 
  (fun A B p => match p with (my_pair _ _ x y) => x end). 

Definition my_snd : (forall A B : Type, (my_prod A B) -> B) := 
  (fun A B p => match p with (my_pair _ _ x y) => y end). 

Definition my_pair_example : my_prod nat bool := my_pair nat bool 7 true.

Compute my_fst nat bool my_pair_example.

Definition my_intermediary : (forall A B H : Type, (H -> A) -> (H -> B) ->
 (H -> my_prod A B)) := (fun A B H f g hv => my_pair A B (f hv) (g hv)).


(** Want to prove universal property **)

(** 3a Empty type **)

Inductive my_empty_set : Set :=.

Definition my_empty_function (A : Type) (x : my_empty_set) : (A : Type) :=
  match x with end.

Check my_empty_function nat.

(** 3b Coproduct type **)

Inductive my_sum (A B:Type) : Type :=
  | my_inl : A -> my_sum A B
  | my_inr : B -> my_sum A B.

Check my_inl.

Check my_inl nat bool 7.

Definition my_coproduct_inter : (forall A B H : Type, (A -> H) -> (B -> H) ->
  ((my_sum A B) -> H)) := (fun A B H f g n => 
  match n with
    | (my_inl _ _ x) => (f x)
    | (my_inr _ _ y) => (g y)
  end).

(** 4a exponential elimination rule **)

Definition expo_elim : (forall X Y : Type, (my_prod (X -> Y) X) -> Y) := 
  (fun X Y v => ((my_fst (X -> Y) X v) (my_snd (X -> Y) X v))).

(** 4b exponential introduction rule **)

Definition expo_intro : (forall A B C : Type, ((my_prod A B) -> C) ->
  (A -> (B -> C))) := (fun A B C pair_fun av bv =>
  pair_fun (my_pair A B av bv)).






(** extra **)

Inductive my_nat : Set :=
  | my_zero : my_nat
  | my_succ : my_nat -> my_nat.



(** finish representing Heyting Algebra ideas
go fo HoTT representation from book, and encode those rules
**)

(** ************** **)

(** 
Sigma _{x : A} B(x) is like  (exists x : A, B(x))
Check ex_intro.
Check ex_proj1.
Definition my_sigma_val : (exists x : bool, (my_B x)) := ex_intro false 7.
https://coq.inria.fr/stdlib/Coq.Init.Logic.html

**)



Definition my_B : bool -> Type := fun b => match b with true => bool | false => nat end.

Check sigT.

Check existT.


Inductive my_sigT (A:Type) (P:A -> Type) : Type :=
    my_existT : forall x:A, P x -> my_sigT A P.

Definition my_sigma_val : (my_sigT bool my_B) :=  my_existT bool my_B false 7.

Definition my_projT1 (A:Type) (P:A -> Type) (x: my_sigT A P) : A := match x with
                                      | my_existT _ _ a _ => a
                                      end.


Check my_projT1.

Compute my_projT1 bool my_B my_sigma_val.




(**
beware of 
Set Implicit Arguments.
in
https://coq.inria.fr/stdlib/Coq.Init.Specif.html

**)

(** *** **)
(* https://coq.inria.fr/library/Coq.Init.Datatypes.html *)

Check Empty_set.

Definition Empty_function (A : Type) (x : Empty_set) : (A : Type) :=
  match x with end.

Check Empty_function nat.

Check unit.

Check tt.

Check sum.
Check inl.

Check prod.
Check pair.
Check 7.

Definition idv (A : Type) (x : A) : A := x.


Compute idv nat 7.

Definition id_strange (t : Type) : t -> t := (fun a => a). 
Compute (id_strange nat 7).





