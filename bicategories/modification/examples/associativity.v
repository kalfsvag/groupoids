Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_transformation.lax_transformation
     lax_transformation.examples.composition
     modification.modification
     general_category.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.

Section Associativity.
  Context `{Univalence}
          {C D : BiCategory}
          {F₁ F₂ F₃ F₄ : LaxFunctor C D}.
  Variable (η₁ : LaxTransformation F₃ F₄)
           (η₂ : LaxTransformation F₂ F₃)
           (η₃ : LaxTransformation F₁ F₂).

  Definition assoc_mod_d
    : modification_d
        (composition.compose η₃ (composition.compose η₂ η₁))
        (composition.compose (composition.compose η₃ η₂) η₁)
    := fun A => assoc (η₁ A) (η₂ A) (η₃ A).

  Definition assoc_d_is_modification : is_modification assoc_mod_d.
  Proof.
    intros A B f ; cbn in *.
    unfold assoc_d, bc_whisker_l, bc_whisker_r.
    rewrite !vcomp_assoc.
    repeat (rewrite <- (vcomp_left_identity (id₂ (η₁ B)))
            ; rewrite interchange
            ; rewrite vcomp_left_identity).
    rewrite !vcomp_assoc.
    repeat (rewrite <- (vcomp_left_identity (id₂ (η₃ A))) ; rewrite interchange).
    rewrite !vcomp_left_identity.
    rewrite !vcomp_assoc.
    apply move_assoc_hcomp_L.
    rewrite <- !vcomp_assoc.
    rewrite vcomp_assoc.
    rewrite <- inverse_pentagon.
    rewrite !vcomp_assoc.
    f_ap.
    rewrite <- !vcomp_assoc.
    rewrite assoc_inv_natural.
    rewrite !vcomp_assoc.
    rewrite hcomp_id₂.
    f_ap.
    rewrite <- !vcomp_assoc.
    rewrite inverse_pentagon_2.
    rewrite !vcomp_assoc.
    repeat f_ap.
    rewrite <- !vcomp_assoc.
    rewrite assoc_inv_natural.
    rewrite !vcomp_assoc.
    repeat f_ap.
    apply move_assoc_hcomp_L.
    rewrite <- !vcomp_assoc.
    rewrite <- inverse_pentagon.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite assoc_right, vcomp_left_identity.
    rewrite <- inverse_pentagon_3.
    rewrite <- !vcomp_assoc.
    repeat f_ap.
    rewrite <- assoc_inv_natural.
    rewrite hcomp_id₂.
    reflexivity.
  Qed.

  Definition assoc_mod
    : modification
        (composition.compose η₃ (composition.compose η₂ η₁))
        (composition.compose (composition.compose η₃ η₂) η₁)
    := Build_Modification assoc_mod_d assoc_d_is_modification.
End Associativity.