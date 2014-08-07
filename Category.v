Require Export Utils.

Generalizable All Variables.

(* X ~> Y is used to indicate morphisms from X to Y in some category.
   X ~{ C }~> Y specifically indicates morphisms in C.

   f ∘ g is composition of morphisms f and g in some category. *)

Reserved Notation "a ~> b" (at level 90, right associativity).
Reserved Notation "f ∘ g" (at level 45).

(* Category is our most basic concept of a category, where the homs are Coq
   functions to Type.  We will (below) use this to build up a notion of
   Category where the homs are curried bifunctors, so that they are presented
   as functors to a category of presheaves (i.e., C^op ⟶ [C, Sets]).  This
   frees us from ever having to talk about Hom functors separately from this
   internal, Coq-friendly notion of homs, and now a bifunctor is just a
   functor to a functor category!

   Every category is defined by objects and morphisms between objects, plus
   the following structure:

   - Every object has an identity morphism.
   - Morphisms compose.
   - Composition respect a monoidal structure: left and right identity using
     the identity morphisms, and associativity. *)

Class Category' :=
{ ob      : Type
; hom     : ob → ob → Type where "a ~> b" := (hom a b)
; id      : ∀ {A}, A ~> A
; compose : ∀ {A B C}, (B ~> C) → (A ~> B) → (A ~> C)
    where "f ∘ g" := (compose f g)

; right_identity : ∀ A B (f : A ~> B), f ∘ id = f
; left_identity  : ∀ A B (f : A ~> B), id ∘ f = f
; comp_assoc     : ∀ A B C D (f : C ~> D) (g : B ~> C) (h : A ~> B),
    f ∘ (g ∘ h) = (f ∘ g) ∘ h
}.

(* Using a Category' in a context requiring a Type provides the ob. *)
Coercion ob : Category' >-> Sortclass.

Notation "a ~> b"       := (hom a b) : category_scope.
Notation "a ~{ C }~> b" := (@hom C a b) (at level 100) : category_scope.
Notation "f ∘ g"        := (compose f g) : category_scope.
Notation "ob/ C"        := (@ob C) (at level 44).

Open Scope category_scope.

Hint Resolve left_identity.
Hint Resolve right_identity.
Hint Resolve comp_assoc.

(* Functor' is built over Category'. *)

Class Functor' (C : Category') (D : Category') :=
{ fobj : C → D
; fmap : ∀ {X Y : C}, (X ~> Y) → (fobj X ~> fobj Y)

; functor_id_law      : ∀ {X : C}, fmap (id (A := X)) = id
; functor_compose_law : ∀ {X Y Z : C} (f : Y ~> Z) (g : X ~> Y),
    fmap f ∘ fmap g = fmap (f ∘ g)
}.

Notation "C ⟶ D" := (Functor' C D) (at level 90, right associativity).

(* Functors used as functions will map objects of categories, similar to the
   way type constructors behave in Haskell. *)
Coercion fobj : Functor' >-> Funclass.

Definition fun_compose
  `(C : Category') `(D : Category') `(E : Category')
  `(F : @Functor' D E) `(G : @Functor' C D) : Functor' C E.
  apply Build_Functor' with
    (fobj := fun x => fobj (fobj x))
    (fmap := fun _ _ f => fmap (fmap f)).
  - intros.
    rewrite functor_id_law.
    apply functor_id_law.
  - intros.
    rewrite functor_compose_law.
    rewrite functor_compose_law.
    reflexivity.
Defined.

Lemma fun_irrelevance `(C : Category') `(D : Category')
  : ∀ (a : C → D) (f g : ∀ {X Y : C}, (X ~> Y) → (a X ~> a Y)) i i' c c',
  @f = @g ->
  {| fobj := @a
   ; fmap := @f
   ; functor_id_law      := i
   ; functor_compose_law := c |} =
  {| fobj := @a
   ; fmap := @g
   ; functor_id_law      := i'
   ; functor_compose_law := c' |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.

(* The opposite category, C^op. *)

Definition Opposite' `(C : Category') : Category'.
  apply Build_Category' with
    (hom     := fun x y => hom y x)
    (id      := @id C)
    (compose := fun a b c f g => g ∘ f).

  intros; apply (@left_identity C).
  intros; apply (@right_identity C).
  intros. symmetry; apply comp_assoc.
Defined.

Notation "C ^op" := (Opposite' C) (at level 90) : category_scope.

Definition Yoneda := Opposite'.

Definition op `{C : Category'} : forall {X Y}, (X ~{C^op}~> Y) -> (Y ~{C}~> X).
Proof. intros. auto. Defined.

Definition unop `{C : Category'} : forall {X Y}, (Y ~{C}~> X) -> (X ~{C^op}~> Y).
Proof. intros. auto. Defined.

Class Natural `(F : @Functor' C D) `(G : @Functor' C D) :=
{ transport  : ∀ {X}, F X ~> G X
; naturality : ∀ {X Y} (f : X ~> Y),
    fmap f ∘ transport = transport ∘ fmap f
}.

Notation "transport/ N" := (@transport _ _ _ _ N _) (at level 44).
Notation "F ⟾ G" := (Natural F G) (at level 90, right associativity).

(* Natural transformations can be applied directly to functorial values to
   perform the functor mapping they imply. *)
Coercion transport : Natural >-> Funclass.

Definition nat_identity `{F : Functor'} : Natural F F.
  apply Build_Natural with (transport := fun _ => id).
  intros.
  rewrite right_identity.
  rewrite left_identity.
  reflexivity.
Defined.

Definition nat_compose
  `{F : @Functor' C D} `{G : @Functor' C D} `{K : @Functor' C D}
  (f : Natural G K) (g : Natural F G) : Natural F K.
  apply Build_Natural
    with (transport := fun X =>
           @transport C D G K f X ∘ @transport C D F G g X).
  intros.
  rewrite comp_assoc.
  rewrite naturality.
  rewrite <- comp_assoc.
  rewrite naturality.
  rewrite comp_assoc.
  reflexivity.
Defined.

Lemma nat_irrelevance `(F : @Functor' C D) `(G : @Functor' C D)
  : ∀ (f g : ∀ {X}, F X ~> G X) n n',
  @f = @g ->
  {| transport := @f; naturality := n |} =
  {| transport := @g; naturality := n' |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
Qed.

(* Nat is the category whose morphisms are natural transformations between
   Functors from C ⟶ D. *)

Instance Nat (C : Category') (D : Category') : Category' :=
{ ob      := Functor' C D
; hom     := @Natural C D
; id      := @nat_identity C D
; compose := fun _ _ _ => nat_compose
}.
Proof.
  - (* right_identity *)
    intros.
    destruct f.
    apply nat_irrelevance.
    extensionality a.
    unfold nat_identity, nat_compose.
    simpl. rewrite right_identity.
    reflexivity.
  - (* left_identity *)
    intros.
    destruct f.
    apply nat_irrelevance.
    extensionality a.
    unfold nat_identity, nat_compose.
    simpl. rewrite left_identity.
    reflexivity.
  - (* comp_assoc *)
    intros.
    destruct f.
    destruct g.
    destruct h.
    apply nat_irrelevance.
    extensionality a.
    unfold nat_identity, nat_compose.
    simpl. rewrite <- comp_assoc.
    reflexivity.
Defined.

Notation "C ⟹ D" := (Nat C D) (at level 90, right associativity).


(* Arr is the category of Coq types and functions, which can also be thought
   of as Coq or Sets (to distinguish from Set).  *)

Program Instance Arr : Category' :=
{ ob      := Type
; hom     := fun X Y => X → Y
; id      := fun _ x => x
; compose := fun _ _ _ f g x => f (g x)
}.

Definition Coq  := Arr.
Definition Sets := Arr.

Definition Copresheaves (C : Category') := C ⟹ Arr.
Definition Presheaves   (C : Category') := C^op ⟹ Arr.

(*
Bifunctors can be curried:

  C × D ⟶ E   -->  C ⟶ D ⟹ E
  ~~~
  (C, D) -> E  -->  C -> D -> E

Where ~~~ should be read as "Morally equivalent to".

Note: We do not need to define Bifunctors as a separate class, since they can
be derived from functors mapping to a category of functors.  So in the
following two definitions, [P] is effectively our bifunctor.

The trick to [bimap] is that both the [Functor] instances we need (for [fmap]
and [fmap1]), and the [Natural] instance, can be found in the category of
functors we're mapping to by applying [P].
*)

Definition fmap1 `{P : C ⟶ D ⟹ E} `(f : X ~{D}~> Y) {A : C} :
  P A X ~{E}~> P A Y := fmap f.

Definition bimap `{P : C ⟶ D ⟹ E} `(f : X ~{C}~> W) `(g : Y ~{D}~> Z) :
  P X Y ~{E}~> P W Z := let N := @fmap _ _ P _ _ f in transport/N ∘ fmap1 g.

Definition contramap `{F : C^op ⟶ D} `(f : X ~{C}~> Y) :
  F Y ~{D}~> F X := fmap (unop f).

Definition dimap `{P : C^op ⟶ D ⟹ E} `(f : X ~{C}~> W) `(g : Y ~{D}~> Z) :
  P W Y ~{E}~> P X Z := bimap (unop f) g.

(* The Identity [Functor] *)

Definition Id `(C : Category') : Functor' C C.
  apply Build_Functor' with
    (fobj := fun X => X)
    (fmap := fun X X f => f); crush.
Defined.

(* Now we have enough machinery to define our desired notion of Category,
   whose homs are curried bifunctors. *)

Program Instance Category : Category' :=
{ ob      := Category'
; hom     := Functor'
; id      := Id
; compose := @fun_compose
}.
Obligation 1.
  unfold fun_compose.
  destruct f.
  apply fun_irrelevance.
  extensionality e.
  extensionality f.
  extensionality g.
  reflexivity.
Defined.
Obligation 2.
  unfold fun_compose.
  destruct f.
  apply fun_irrelevance.
  extensionality e.
  extensionality f.
  extensionality g.
  reflexivity.
Defined.
Obligation 3.
  unfold fun_compose.
  destruct f.
  apply fun_irrelevance.
  extensionality e.
  extensionality f.
  reflexivity.
Defined.
