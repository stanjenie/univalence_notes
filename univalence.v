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


(* Polymorphic functions *)
Definition id : forall (A : Type), A -> A := fun (A : Type) (x : A) => x. 

Definition swap : forall (A B C: Type), (A -> B -> C) -> (B -> A -> C) := 
  fun (A B C : Type) (g : A -> B -> C) (b : B) (a: A) => g a b. 

Inductive Unit := point. 

Definition true_unit : True <-> Unit := conj (fun _ => point) (fun _ => I).

Definition lf : forall {A B : Prop}, A /\ B -> A :=
  fun {A B : Prop} (p : A /\ B) => match p with
                        | conj a b => a end.

Definition rt : forall {A B : Prop}, A /\ B -> B :=
  fun {A B : Prop} (p : A /\ B) => match p with
                                     | conj a b => b end.

Definition unit_contractible : forall a b : Unit, a = b :=
  fun (a b : Unit) =>
    match a, b with
    | point, point => eq_refl end.

Definition true_contractible : forall a b : True, a = b :=
  fun (a b : True) =>
    match a, b with
      | I, I => eq_refl end.

End HoTT_1_4.

Module HoTT_1_5.

Inductive prod' (A B : Type) := pair' : A -> B -> prod' A B.

Definition prod_elim : 
  forall {A B C : Type} (g : A -> B -> C), A * B -> C. 
Proof.
  intros A B C g [a b]. exact (g a b).
Show Proof.
Defined.

Type @prod_elim. (* forall A B C : Type, (A -> B -> C) -> A * B -> C) *)

(* comparison with other coq-defined defs *)
Type prod_rect.
(* forall (A B : Type) (P : A * B -> Type),
    (forall (a : A) (b : B), P (a, b)) -> forall p : A * B, P p *)

Type prod_ind. (* = ind type *)
(* forall (A B : Type) (P : A * B -> Prop), 
    (forall (a : A) (b : B), P (a, b)) -> forall p : A * B, P p *)
          
Type prod_rec.
(* forall (A B : Type) (P : A * B -> Set),
    (forall (a : A) (b : B), P (a, b)) -> forall p : A * B, P p *)

Definition Unit_rec' : forall (C : Type), C -> HoTT_1_4.Unit -> C. 
Proof.
  intros C c []. exact c.
Show Proof.
Defined.

Type Unit_rec'.
(* forall C : Type, C -> Unit -> C *)

Type True_rect.
(* forall P : Type, P -> True -> P *)

Definition pr1 : 
  forall {A B : Type}, A * B -> A := fun A B => prod_elim (fun a b => a).

Definition pr2 :
  forall {A B : Type}, A * B -> B := fun A B => prod_elim (fun a b => b).

Definition prod_uniq : forall {A B : Type} (x : A * B), (pr1(x), pr2(x)) = x.
Proof.
  intros A B [a b]. reflexivity.
Show Proof.
Defined.

Definition Unit := HoTT_1_4.Unit.
Definition point := HoTT_1_4.point.

Definition unit_ind : 
  forall C : Unit -> Type, C(point) -> (forall x : Unit, C(x)) :=
  fun C C_pt x => match x with point => C_pt end.

Type True_ind.
(* forall P : Prop, P -> True -> P *)
(** Notice that HoTT _ind is not the same as Coq's _ind. *)

Definition unit_uniq :
  forall x : Unit, x = point := fun x => match x with point => eq_refl end.
Compute unit_uniq.

Definition unit_uniq' :
  forall x : Unit, x = point := unit_ind (fun x => x = point) eq_refl.
Compute unit_uniq'.

End HoTT_1_5.

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

End HoTT_1_6.

(** Coproduct types *)
Module HoTT_1_7.

Inductive empty : Type :=. 

(* recursor for the coproduct type *)
Definition sum_rec : forall {A B : Type} (C : Type), (A -> C) -> (B -> C) -> (A + B -> C).
Proof.
  intros A B C g0 g1 [a | b].
  - exact (g0 a).
  - exact (g1 b).
Show Proof.
Defined.

(* recursor for the empty type *)
Definition empty_rec' : forall C : Type, empty -> C.
Proof.
  intros C [].
Show Proof.
Defined.

(* inductor for the coproduct type *)
Definition sum_ind : forall {A B : Type} (C : A + B -> Type),
    (forall a : A, C (inl a)) -> (forall b : B, C (inr b)) -> 
    (forall x : A + B, C x).
Proof.
  intros A B C g0 g1 [a | b].
  - exact (g0 a).
  - exact (g1 b).
Show Proof.
Defined.

(* inductor for the empty type *)
Definition empty_ind' : forall (C : empty -> Type) (z : empty), C z.
Proof.
  intros C [].
Show Proof.
Defined.

End HoTT_1_7.

Module HoTT_1_8.

Definition Unit := HoTT_1_4.Unit.
Definition point := HoTT_1_4.point.

Definition bool : Type := sum Unit Unit.

(* recursor on bool type *)
Definition bool_rec' : forall (C : Type), C -> C -> bool -> C.
Proof.
  intros C c0 c1 [[] | []].
  - exact c0.
  - exact c1.
Show Proof.
Defined.

(* Observe that the rec proofs constructed here are not proof-independent: indeed,
  a natural proof of bool_rec would be as follows: *)

Definition bool_rec_faulty : forall (C : Type), C -> C -> bool -> C :=
  fun C c _ _ => c.

(* While this definition type-checks, it clearly does not capture the expected
semantics of the type bool; using this as a recursor, in fact, would lend it the
behavior of the unit type. That this is possible shows bool -> unit. *)

Definition false' : bool := inl point.
Definition true' : bool := inr point.

(* inductor on bool type *)
Definition bool_ind' : forall (C : bool -> Type), 
    C false' -> C true' -> forall x : bool, C x.
Proof.
  intros C c0 c1 [[] | []].
  - exact c0.
  - exact c1.
Show Proof.
Defined.

(* Note that the proof for induction, however, is in fact the most natural construction
of the function, and we shall later show uniqueness. In this manner, the semantics
of the bool type may be predicated purely on the type of the inductor. *)

Definition thm_1_8_1 : forall x : bool, (x = false') + (x = true').
Proof.
  apply bool_ind'.
  - apply (inl eq_refl).
  - apply (inr eq_refl).
Show Proof.
Defined.

Definition sum' (A B : Type) := sigT (fun x : bool => bool_rec' Type A B x).
Definition inl' {A B: Type} (a : A) : (sum' A B) := 
  existT (fun x : bool => bool_rec' Type A B x) false' a.
Definition inr' {A B : Type} (b : B) : (sum' A B) :=
  existT (fun x : bool => bool_rec' Type A B x) true' b.

(* Exercise : Derive induction principle for coproducts from this. *)

Definition prod' (A B : Type) := forall x : bool, bool_rec' Type A B x.
Definition pair' {A B : Type} (a : A) (b : B) : prod' A B :=
  bool_ind' (bool_rec' Type A B) a b.
Definition pr1' {A B : Type} (p : prod' A B) := p false'.
Definition pr2' {A B : Type} (p : prod' A B) := p true'.

Compute pr1' (pair' 3 4). (* 3 : bool_rec' Type nat nat false' *)
Compute (bool_rec' Type nat nat false'). (* nat : Type *)

(* However this product has an extensional flavor to it. *)
(** TODO : Exercises and proofs of equivalence *)

End HoTT_1_8.

