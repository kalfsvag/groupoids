Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation.
Require Import GR.bicategories.bicategories.
Require Import GR.bicategories.lax_functors.
(* From GR.groupoid.grpd_bicategory Require Import *)
(*      grpd_bicategory. *)

Class is_univalent (C : PreCategory)
  := obj_cat : IsCategory C.

(** now let's discuss some examples of groupoids.
    The first example is the paths on a certain type.
 *)
Definition path_category (X : 1 -Type) : PreCategory :=
  (Build_PreCategory 
     (fun x y : X => BuildhSet (x = y))
     (fun _ => idpath)
     (fun _ _ _ p q => q @ p)
     (fun _ _ _ _ => concat_p_pp)
     (fun _ _ => concat_p1)
     (fun _ _ => concat_1p)
     _). 

Global Instance path_category_univalent (X : 1 -Type)
  : is_univalent (path_category X).
Proof.
  unfold path_category, is_univalent.
  apply _.
Defined.

Section PathGroupoidFunctor.
  Context `{Univalence}.
  
  Definition ap_functor {X Y : 1 -Type}
    : one_types ⟦X,Y⟧ -> PreCat⟦path_category X,path_category Y⟧
    := fun f =>
         Build_Functor
           (path_category X)
           (path_category Y)
           f
           (fun _ _ => ap f)
           (fun _ _ _ => ap_pp f)
           (fun _ => idpath).

  Definition path_category_map (X Y : 1 -Type)
    : Functor (one_types⟦X,Y⟧) (PreCat⟦path_category X,path_category Y⟧).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _).
    - exact ap_functor.
    - simpl ; intros f g p.
      simple refine (Build_NaturalTransformation _ _ _ _) ; simpl.
      + exact (ap10 p).
      + intros x y m.
        induction m, p ; simpl.
        reflexivity.
    - simpl ; intros f g h p q.
      apply path_natural_transformation ; simpl.
      intros x.
      apply ap10_pp.
    - simpl ; intros f.
      apply path_natural_transformation ; simpl.
      intros x.
      reflexivity.
  Defined.

  Definition path_category_map_compose
             {X Y Z : 1 -Type}
             (g : Y -> Z)
             (f : X -> Y)
    : NaturalTransformation
        ((path_category_map Y Z) g o (path_category_map X Y) f)
        ((path_category_map X Z) (fun x : X => g (f x))).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _) ; cbn.
    - reflexivity.
    - intros x y p ; cbn.
      refine (concat_p1 _ @ _^ @ (concat_1p _)^).
      apply ap_compose.
  Defined.

  Definition path_category_map_compose_inv
             {X Y Z : 1 -Type}
             (g : Y -> Z)
             (f : X -> Y)
    : NaturalTransformation
        ((path_category_map X Z) (fun x : X => g (f x)))
        ((path_category_map Y Z) g o (path_category_map X Y) f).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _) ; cbn.
    - reflexivity.
    - intros x y p ; cbn.
      refine (concat_p1 _ @ _ @ (concat_1p _)^).
      apply ap_compose.
  Defined.

  Definition path_category_map_id (X : 1 -Type)
    : NaturalTransformation 1%functor ((path_category_map X X) idmap).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _) ; cbn.
    - reflexivity.
    - intros x y p ; cbn.
      refine (concat_p1 _ @ _^ @ (concat_1p _)^).
      apply ap_idmap.
  Defined.

  Definition path_category_map_id_inv (X : 1 -Type)
    : NaturalTransformation ((path_category_map X X) idmap) 1%functor.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _) ; cbn.
    - reflexivity.
    - intros x y p ; cbn.
      refine (concat_p1 _ @ _ @ (concat_1p _)^).
      apply ap_idmap.
  Defined.
  
  Definition ap_functor_natural
             {X Y : one_types}
             {f g : one_types⟦X,Y⟧}
             (p : f ==> g)
    : NaturalTransformation (ap_functor f) (ap_functor g).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _) ; simpl.
    - exact (ap10 p).
    - intros x y q ; simpl.
      induction p, q.
      reflexivity.
  Defined.

  Definition path_functor_rd
    : PseudoFunctor_d one_types PreCat.
  Proof.
    make_pseudo_functor.
    - exact path_category.
    - exact path_category_map.
    - exact @ap_functor_natural.
    - intros X Y Z.
      exact path_category_map_compose.
    - exact path_category_map_id.
    - intros X Y Z.
      exact path_category_map_compose_inv.
    - exact path_category_map_id_inv.
  Defined.

  Definition path_functor_rd_is_pseudo
    : is_pseudo_functor_p path_functor_rd.
  Proof.
    make_is_pseudo.
    - intros X Y f.
      apply path_natural_transformation.
      intro ; reflexivity.
    - intros X Y f g h p q.
      induction p, q.
      apply path_natural_transformation.
      intro ; reflexivity.
    - intros X Y Z f₁ f₂ g₁ g₂ p q.
      induction p, q.
      apply path_natural_transformation.
      intro x ; cbn in *.
      rewrite ap10_path_forall.
      reflexivity.
    - intros X Y f.
      apply path_natural_transformation.
      intro ; reflexivity.
    - intros X Y f.
      apply path_natural_transformation.
      intro ; reflexivity.
    - intros W X Y Z h g f.
      apply path_natural_transformation.
      intro ; reflexivity.
    - intros X Y Z g f.
      apply path_natural_transformation.
      intro ; reflexivity.
    - intros X Y Z g f.
      apply path_natural_transformation.
      intro ; reflexivity.
    - intros X.
      apply path_natural_transformation.
      intro ; reflexivity.
    - intros X.
      apply path_natural_transformation.
      intro ; reflexivity.
  Qed.

  Definition path_category_functor
    : PseudoFunctor one_types PreCat
    := Build_PseudoFunctor path_functor_rd path_functor_rd_is_pseudo.
End PathGroupoidFunctor.