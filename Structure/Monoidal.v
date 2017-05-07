Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Product.
Require Export Category.Instance.Nat.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Monoidal.

Context `{C : Category}.

Reserved Infix "⨂" (at level 30, right associativity).

Class Monoidal := {
  tensor : C ∏ C ⟶ C
    where "x ⨂ y" := (tensor (x, y));

  I : C;

  unit_left  {X} : I ⨂ X ≅ X;
  unit_right {X} : X ⨂ I ≅ X;

  tensor_assoc {X Y Z} : (X ⨂ Y) ⨂ Z ≅ X ⨂ (Y ⨂ Z)
}.

Notation "X ⨂ Y" := (tensor (X, Y)) (at level 30, right associativity).

Class SymmetricMonoidal `{Monoidal} := {
  swap {X Y} : X ⨂ Y ≅ Y ⨂ X
}.

End Monoidal.

Notation "X ⨂ Y" := (@tensor _ _ (X, Y)) (at level 30, right associativity).

Local Obligation Tactic := program_simpl.

(* This reflects the fact that categories are themselves "monoidoids", or
   monoidal with respect to identity and composition.  *)

Program Definition Composition_Monoidal `{C : Category} :
  @Monoidal ([C, C]) := {|
  tensor :=
    {| fobj := fun p => Compose (fst p) (snd p)
     ; fmap := fun F G N =>
         {| transform := fun x =>
              transform[fst N] (snd G x) ∘ fmap[fst F] (transform[snd N] x) |}
     |};
  I := Id
|}.
Next Obligation.
  simpl in *.
  rewrite <- natural_transformation.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- natural_transformation.
  rewrite <- !comp_assoc.
  rewrite <- natural_transformation.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- natural_transformation.
  reflexivity.
Qed.
Next Obligation.
  proper; simplify; simpl in *.
  rewrite a, b.
  reflexivity.
Qed.
Next Obligation.
  simplify; simpl in *.
  rewrite !fmap_id; cat.
Qed.
Next Obligation.
  simplify; simpl in *.
  rewrite <- !comp_assoc.
  apply compose_respects.
    reflexivity.
  rewrite <- !natural_transformation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  reflexivity.
Qed.
Next Obligation. constructive; cat. Defined.
Next Obligation. constructive; cat. Defined.
Next Obligation. constructive; cat. Defined.

(* Every cartesian category with terminal objects gives rise to a monoidal
   category taking the terminal object as unit, and the tensor as product. *)

Require Import Category.Functor.Product.Internal.

(* Any cartesian category with terminal objects is monoidal with respect to
   its internal product functor. *)

Program Definition InternalProduct_Monoidal
        `{C : Category} `{@Cartesian C} `{@Terminal C} : @Monoidal C := {|
  tensor := InternalProductFunctor C;
  I := One
|}.

Require Import Category.Functor.Bifunctor.

Local Obligation Tactic := simpl; intros.

(* Any product of monoidal categories is monoidal. *)

Program Instance Product_Monoidal
        `{C : Category} `{@Monoidal C} `{D : Category} `{@Monoidal D} :
  @Monoidal (C ∏ D) := {
  tensor :=
    {| fobj := fun x => (fst (fst x) ⨂ fst (snd x),
                         snd (fst x) ⨂ snd (snd x))
     ; fmap := fun _ _ f => (bimap (fst (fst f)) (fst (snd f)),
                             bimap (snd (fst f)) (snd (snd f))) |};
  I := (@I C _, @I D _)
}.
Next Obligation.
  exact H.
Defined.
Next Obligation.
  exact H0.
Defined.
Next Obligation.
  simplify; simpl in *.
  proper; simplify; simpl in *.
    rewrite a0, a.
    reflexivity.
  rewrite b0, b1.
  reflexivity.
Qed.
Next Obligation.
  simplify; simpl in *;
  rewrite <- fmap_id;
  apply fmap_respects; cat.
Qed.
Next Obligation.
  simplify; simpl in *;
  rewrite bimap_comp;
  reflexivity.
Qed.
Next Obligation.
  isomorphism; simpl; simplify.
  - apply (to unit_left).
  - apply (to unit_left).
  - apply (from unit_left).
  - apply (from unit_left).
  - apply iso_to_from.
  - apply iso_to_from.
  - apply iso_from_to.
  - apply iso_from_to.
Defined.
Next Obligation.
  isomorphism; simpl; simplify; simpl.
  - apply (to unit_right).
  - apply (to unit_right).
  - apply (from unit_right).
  - apply (from unit_right).
  - apply iso_to_from.
  - apply iso_to_from.
  - apply iso_from_to.
  - apply iso_from_to.
Defined.
Next Obligation.
  isomorphism; simpl; simplify; simpl.
  - apply (to tensor_assoc).
  - apply (to tensor_assoc).
  - apply (from tensor_assoc).
  - apply (from tensor_assoc).
  - apply iso_to_from.
  - apply iso_to_from.
  - apply iso_from_to.
  - apply iso_from_to.
Defined.
