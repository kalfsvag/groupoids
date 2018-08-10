Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     lax_transformation.examples.identity
     lax_transformation.examples.composition
     modification.modification
     general_category.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.

Section RightIdentity.
  Context `{Univalence}
          {C D : BiCategory}
          {F₁ F₂ : LaxFunctor C D}.
  Variable (η : LaxTransformation F₁ F₂).

  Definition right_identity_mod_d
    : modification_d (composition.compose (identity_transformation F₁) η) η
    := fun A => right_unit (η A).

  Definition right_identity_is_mod : is_modification right_identity_mod_d.
  Proof.
    intros A B f ; cbn in *.
    unfold bc_whisker_l, bc_whisker_r, right_identity_mod_d.
    rewrite !vcomp_assoc.
    rewrite <- (vcomp_left_identity (id₂ (η B))).
    rewrite interchange.
    rewrite !vcomp_assoc.
    rewrite triangle_r.
    rewrite !vcomp_assoc.
    rewrite (ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite assoc_left.
    rewrite vcomp_left_identity.
    rewrite <- !vcomp_assoc.
    rewrite <- interchange.
    rewrite left_unit_left.
    rewrite vcomp_left_identity.
    rewrite hcomp_id₂.
    rewrite vcomp_left_identity.
    pose @right_unit_assoc as p.
    unfold bc_whisker_l in p.
    rewrite <- p ; clear p.
    rewrite right_unit_natural.
    rewrite vcomp_assoc.
    rewrite right_unit_assoc.
    unfold bc_whisker_r.
    rewrite !vcomp_assoc.
    rewrite assoc_left.
    rewrite vcomp_right_identity.
    reflexivity.
  Qed.

  Definition right_identity_mod
    : modification (composition.compose (identity_transformation F₁) η) η
    := Build_Modification right_identity_mod_d right_identity_is_mod.

  Global Instance right_identity_mod_pseudo
    : is_pseudo_modification right_identity_mod.
  Proof.
    split ; apply _.
  Defined.
End RightIdentity.
