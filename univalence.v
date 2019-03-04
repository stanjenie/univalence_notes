(** 1.2 Function Types *)
Module HoTT_1_2.

Definition f : nat -> nat := fun x => x + x. 

Compute (f 2). (** 2 + 2 = 4 *)

Type (fun (x : nat) => x + x). (** nat -> nat *)

(* uniqueness principle for function types *)
Theorem fun_uniq : 
  forall (A B : Type) (f : A -> B), f = (fun x => f x).
Proof. 
  intros A B f.
  exact eq_refl. 
Qed.

End HoTT_1_2. 

(** 1.3 Universes and Families *)
Module HoTT_1_3. 

Set Printing Universes. 

Inductive Unit : Type := point. 

Definition type_family_example : nat -> Type :=
  fix TFEfix (x : nat) := match x with
                     | O => Prop
                     | S x' => sum Unit (TFEfix x') end. 

Type type_family_example. (* nat -> Type@{Top.10} *) 

Definition constant_type_family (B : Type) : forall {A : Type}, A -> Type :=
  fun {A : Type} (x : A) => B. 

End HoTT_1_3.
 
(** 1.4 Dependent Function Types *)
Module HoTT_1_4.

(* the dependent product type into a constant type family is equivalent to the function type *)
Lemma prod_const__fun : forall A B : Type, (forall x : A, B) = (A -> B). 
Proof. 
  reflexivity.
Show Proof.
Qed.

End HoTT_1_4.

(* 1.6 Dependent Pair Types *)
Module HoTT_1_6.

Definition constant_type_family := HoTT_1_3.constant_type_family.

Inductive sig1 {A : Type} (P : A -> Type) : Type :=
  existP : forall x:A, P x -> sig1 P.

Definition dpt_test1 : forall A : Type, nat := fun x => 3.
Definition dpt_test2 : forall A : Type, A -> Type := fun x y => nat.
Definition dpt_test3 : forall A B: Type, nat -> Prop := fun x y z => (z = z).
Definition dpt_test4 : forall A B : Type, nat -> Type := fun x y z => nat. 
Definition dpt_test5 : forall A: Type, A -> (A -> Type) := fun x y z => nat. 
Definition dpt_test6 : forall A : Type, 3 = 3 := fun x => eq_refl. 
Definition dpt_test7 : forall A : Type, 3 = 3 -> nat := fun x y => 3. 

Type (existP (fun x => x)). 

Definition iffT : Type -> Type -> Type := fun A B => prod (A -> B) (B -> A).  

(* the dependent pair type over a constant type is equivalent to the cartesian product *)
Definition sum_const__prod : forall A B : Type, iffT (sigT (fun a:A => B)) (prod A B). 
Proof. 
  intros A B. split.
  - intros [a b]. exact (pair a b). 
  - intros [a b]. exact (existT (fun _ => B) a b). 
Show Proof. 
Defined.

Definition pr1 : forall {A : Type} {B : A -> Type}, (sigT (fun x:A => B x)) -> A. 
Proof.
  intros A B [a _].
  exact a.
Show Proof. 
Defined.

 Definition pr2 : forall {A : Type} {B : A -> Type} (p : sigT (fun x:A => B x)), B (pr1 p). 
Proof. 
  intros A B [a b].
  simpl. exact b. 
Show Proof. 
Defined.

Definition sum_elim : 
  forall {A : Type} {B : A -> Type} {C : (sigT (fun (x : A) => B x)) -> Type}
                                           (a : A) (b : B a), C (existT _ a b).
Proof. Admitted. 

Definition sum_elim_f : 
  forall {A : Type} {B : A -> Type} {C : (sigT (fun (x : A) => B x)) -> Type}
         (p : sigT (fun (x : A) => B x)), C p. 
Proof. 
  intros A B C [a b]. 
  exact (sum_elim a b).
Defined.

(* recursor for dependent pair types *)
Definition sig_rec : forall {A : Type} {B : A -> Type} {C : Type}, 
    (forall x : A, B x -> C) -> (sigT (fun x:A => B x)) -> C. 
Proof. 
  intros A B C g [a b]. 
  exact (g a b).
Show Proof. 
Defined. 

(* inductor for dependent pair types *)
Definition sig_ind : forall {A : Type} {B : A -> Type} (C : (sigT (fun x : A => B x)) -> Type),
                            (forall (a : A) (b : B a), C (existT _ a b)) ->
                            (forall (p : (sigT (fun x : A => B x))), C p). 
Proof.
  intros A B C g [a b]. 
  exact (g a b). 
Show Proof. 
Defined. 

(* The type-theoretic axiom of choice *)
Definition sig_ac : forall {A B : Type} {R : A -> B -> Type}, 
    (forall (x : A), sigT (fun y : B => R x y)) -> 
    (sigT (fun f : A -> B => forall x : A, R x (f x))).
Proof.
  intros A B R g. 
  pose (fun f : A -> B => forall x : A, R x (f x)).
  exact (existT T (fun x => pr1 (g x)) (fun x => pr2 (g x))). 
Show Proof. 
Defined. 

(* We may define magmas and pointed magmas in terms of dependent pair types. *)
Definition Magma : Type := sigT (fun A : Type => A -> A -> A). 
Definition PointedMagma : Type := sigT (fun A : Type => prod (A -> A -> A) A). 



