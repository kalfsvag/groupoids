Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation GroupoidCategory FunctorCategory.
Require Import GR.bicategories.bicategories.

(** The definition of groupoids. *)
Definition groupoid := {C : PreCategory & IsGroupoid C}.

Class is_univalent (G : groupoid)
  := obj_cat : IsCategory G.1.

Global Instance is_univalent_ishprop `{Funext} (G : groupoid)
  : IsHProp (is_univalent G).
Proof.
  unfold is_univalent.
  apply _.
Defined.

(** The structure of groupoids *)

(** The underlying type of objects. *)
Definition under (G : groupoid) : Type
  := object G.1.

Global Instance univalent_one_type (G : groupoid) `{is_univalent G}
  : IsTrunc 1 (under G).
Proof.
  unfold is_univalent, under in *.
  apply _.
Defined.

Coercion grpd_to_type := under.

(** The homsets. *)
Definition hom (G : groupoid) : G -> G -> hSet
  := fun x y => BuildhSet (morphism G.1 x y)%morphism.

Coercion hom : groupoid >-> Funclass.

(** The unit element. *)
Definition e {G : groupoid} (x : G) : G x x
  := 1%morphism.

(** Composition. *)
Definition comp {G : groupoid} {x y z : G}
  : G x y -> G y z -> G x z
  := fun g h => (h o g)%morphism.

Notation "p ● q" := (comp p q) (at level 40). (* \ci *)

(** Inverses. *)
Definition inv {G : groupoid} {x y : G}
  : G x y -> G y x
  := fun g => @morphism_inverse _ _ _ g (G.2 _ _ g).

(** Left associativity. *)
Definition grpd_left_assoc
           {G : groupoid}
           {v x y z : G}
           (p : G v x) (q : G x y) (r : G y z)
  : (p ● q) ● r = p ● (q ● r)
  := (associativity _ v x y z p q r)^.

(** Right associativity. *)
Definition grpd_right_assoc
           {G : groupoid}
           {v x y z : G}
           (p : hom G v x) (q : hom G x y) (r : hom G y z)
  : p ● (q ● r) = (p ● q) ● r
  := associativity _ v x y z p q r.

(** Right neutrality. *)
Definition grpd_right_identity
           {G : groupoid}
           {x y : G}
           (p : G x y)
  : p ● e y = p
  := left_identity _ x y p.

(** Left neutrality. *)
Definition grpd_left_identity
           {G : groupoid}
           {x y : G}
           (p : G x y)
  : e x ● p = p
  := right_identity _ x y p.

(** Right inverse. *)
Definition grpd_right_inverse
           {G : groupoid}
           {x y : G}
           (p : G x y)
  : p ● inv p = e x
  := @left_inverse _ x y p (G.2 x y p).

(** Left inverse. *)
Definition grpd_left_inverse
           {G : groupoid}
           {x y : G}
           (p : G x y)
  : inv p ● p = e y
  := @right_inverse _ x y p (G.2 x y p).

(** A function for building groupoids. *)
Definition Build_grpd
           (obj : Type)
           (hom : obj -> obj -> hSet)
           (e : forall (x : obj), hom x x)
           (inv : forall {x y : obj}, hom x y -> hom y x)
           (comp : forall {x y z : obj}, hom x y -> hom y z -> hom x z)
           (assoc : forall (x y z v : obj) (p : hom v x) (q : hom x y) (r : hom y z),
               comp p (comp q r) = comp (comp p q) r)
           (ec : forall (x y : obj) (p : hom x y),
               comp (e x) p = p)
           (ce : forall (x y : obj) (p : hom x y),
               comp p (e y) = p)
           (ic : forall (x y : obj) (p : hom x y),
               comp (inv p) p = e y)
           (ci : forall (x y : obj) (p : hom x y),
               comp p (inv p) = e x)
  : groupoid.
Proof.
  simple refine (@Build_PreCategory
                   obj
                   hom
                   e
                   (fun _ _ _ p q => comp _ _ _ q p) _ _ _ _;_).
  - cbn ; intros.
    apply assoc.
  - cbn ; intros.
    apply ce.
  - cbn ; intros.
    apply ec.
  - intros x y g ; cbn in *.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    + exact (inv _ _ g).
    + apply ci.
    + apply ic.
Defined.

(** Groupoid functors *)
Definition grpd_functor `{Funext} (G₁ G₂ : groupoid) : PreCategory
  := functor_category G₁.1 G₂.1.

(** The object part of a functor. *)
Definition grpd_object_of `{Funext} {G₁ G₂ : groupoid} (F : grpd_functor G₁ G₂)
  : under G₁ -> under G₂
  := object_of F.

(** The morphism part of a functor. *)
Definition grpd_morphism_of `{Funext} {G₁ G₂ : groupoid} (F : grpd_functor G₁ G₂)
  : forall {x y : under G₁},
    hom G₁ x y -> hom G₂ (grpd_object_of F x) (grpd_object_of F y)
  := morphism_of F.

(** Functors preserve the unit. *)
Definition grpd_identity_of `{Funext} {G₁ G₂ : groupoid} (F : grpd_functor G₁ G₂)
  : forall (x : under G₁), grpd_morphism_of F (e x) = e (grpd_object_of F x)
  := identity_of F.

(** Functors preserve the multiplication. *)
Definition grpd_composition_of `{Funext} {G₁ G₂ : groupoid} (F : grpd_functor G₁ G₂)
  : forall {x y z : under G₁} (p : hom G₁ x y) (q : hom G₁ y z),
    grpd_morphism_of F (p ● q) = grpd_morphism_of F p ● grpd_morphism_of F q
  := composition_of F.

(** Functors preserve inverses. *)
Definition grpd_inverse_of `{Funext} {G₁ G₂ : groupoid} (F : grpd_functor G₁ G₂)
  : forall {x y : under G₁} (p : hom G₁ x y),
    grpd_morphism_of F (inv p) = inv (grpd_morphism_of F p).
Proof.
  intros x y p.
  apply iso_moveL_1V.
  refine (((grpd_composition_of F p (inv p))^ @ _ @ grpd_identity_of F x)).
  apply (ap (grpd_morphism_of F)).
  apply grpd_right_inverse.
Defined.

(** We have a bicategory of groupoids. *)
Definition grpd `{Funext} : BiCategory
  := full_sub PreCat (fun C => BuildhProp (IsGroupoid C)).

(** We have a bicategory of univalent groupoids. *)
Definition univalent_grpd `{Funext} : BiCategory
  := full_sub grpd (fun G => BuildhProp (is_univalent G)).

(** Note: it has the expected objects and morphisms. *)
Definition grpd_obj `{Funext} : Obj grpd = groupoid
  := idpath.

Definition grpd_hom `{Funext} : Hom grpd = grpd_functor
  := idpath.

Definition grpd_21 `{Funext} : is_21 grpd.
Proof.
  intros G₁ G₂ F₁ F₂ α ; simpl in *.
  simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
  - simple refine (Build_NaturalTransformation _ _ _ _).
    + intros C.
      apply G₂.
      exact (α C).
    + intros x y g ; cbn.
      refine (iso_moveR_Mp _ _ _) ; cbn.
      refine (_ @ associativity _ _ _ _ _ _ _ _).
      apply iso_moveL_pV.
      apply α.
  - apply path_natural_transformation ; simpl.
    intro x.
    apply left_inverse.
  - apply path_natural_transformation ; simpl.
    intro x.
    apply right_inverse.
Defined.