Require Import HoTT.
From HoTT.Categories Require Export Category.
From HoTT.Categories Require Import Functor NaturalTransformation FunctorCategory.

Definition const_functor
           {C D : PreCategory}
           (X : D)
  : Functor C D
  := Build_Functor C
                   D
                   (fun _ => X)
                   (fun _ _ _ => Category.identity X)
                   (fun _ _ _ _ _ => (left_identity _ _ _ _)^)
                   (fun _ => idpath).

Definition apply_functor
           `{Funext}
           {C : PreCategory}
           (D : PreCategory)
           (X : C)
  : Functor (C -> D) D.
Proof.
  simple refine (Build_Functor _ _ _ _ _ _).
  - exact (fun F => object_of F X).
  - exact (fun F G η => η X).
  - reflexivity.
  - reflexivity.
Defined.

Definition assoc_prod (C D E : PreCategory)
  : Functor ((C * D) * E) (C * (D * E))
  := fst o fst * (snd o fst * snd).

Definition pair
           {C₁ D₁ C₂ D₂ : PreCategory}
           {F₁ F₂ : Functor C₁ C₂}
           {G₁ G₂ : Functor D₁ D₂}
           (af : NaturalTransformation F₁ F₂)
           (ag : NaturalTransformation G₁ G₂)
  : NaturalTransformation (F₁,G₁) (F₂,G₂).
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - exact (fun X => (af (fst X),ag (snd X))).
  - exact (fun X Y f => path_prod' (commutes af _ _ _) (commutes ag _ _ _)).
Defined.

Definition inverse_compose
           {C : PreCategory}
           {X Y Z : C}
           (g : morphism C Y Z) (f : morphism C X Y)
           `{IsIsomorphism C _ _ f} `{IsIsomorphism C _ _ g}
  : ((g o f)^-1 = f^-1 o g^-1)%morphism
  := idpath.

Definition inverse_id
           {C : PreCategory}
           (X : C)
  : (1^-1 = Core.identity X)%morphism
  := idpath.

Global Instance iso_pair
       {C D : PreCategory}
       {XC YC : C}
       {XD YD : D}
       (f : morphism C XC YC) (g : morphism D XD YD)
       `{IsIsomorphism C _ _ f} `{IsIsomorphism D _ _ g}
  : IsIsomorphism ((f,g) : morphism (Category.Prod.prod C D) (XC,XD) (YC,YD)).
Proof.
  simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
  - exact (f^-1,g^-1)%morphism.
  - exact (path_prod' left_inverse left_inverse).
  - exact (path_prod' right_inverse right_inverse).
Defined.

Definition inverse_pair
           {C D : PreCategory}
           {XC YC : C}
           {XD YD : D}
           (f : morphism C XC YC) (g : morphism D XD YD)
           `{IsIsomorphism C _ _ f} `{IsIsomorphism D _ _ g}
  : (((f,g) : morphism (Category.Prod.prod C D) (XC,XD) (YC,YD))^-1)%morphism
    = (f^-1,g^-1)%morphism
  := idpath.

Definition inverse_of
           {C D : PreCategory}
           (F : Functor C D)
           {X Y : C}
           (f : morphism C X Y)
           `{IsIsomorphism C _ _ f}
  : (morphism_of F (f^-1) = (morphism_of F f)^-1)%morphism
  := idpath.

Definition path_inverse
           {C : PreCategory}
           {X Y : C}
           (f g : morphism C X Y)
           `{IsIsomorphism C _ _ f} `{IsIsomorphism C _ _ g}
  : f = g -> (f^-1 = g^-1)%morphism.
Proof.
  intros p ; induction p.
  refine ((right_identity _ _ _ _)^ @ _).
  refine (ap _ (@right_inverse _ _ _ f _)^ @ _).
  refine ((associativity _ _ _ _ _ _ _ _)^ @ _).
  refine (ap (fun z => z o _)%morphism (@left_inverse _ _ _ f _) @ _).
  apply left_identity.
Defined.

Definition iso_component
           `{Funext}
           {C D : PreCategory}
           {F G : Functor C D}
           (η : NaturalTransformation F G)
           `{IsIsomorphism (_ -> _) _ _ η}
           (X : C)
  : Core.components_of (@morphism_inverse (_ -> _) _ _ η _) X
    =
    morphism_inverse (Core.components_of η X).
Proof.
  reflexivity.
Defined.

Definition nice_path_functor'
           `{Funext}
           {C D : PreCategory}
           {F G : Functor C D}
           (FGO : object_of F = G)
           (FGM : forall {X Y : C} (f : morphism C X Y),
               ((@morphism_isomorphic _ _ _ (Category.Morphisms.idtoiso D (ap10 FGO Y)))
                 o (morphism_of F f)
                 o morphism_inverse (Category.Morphisms.idtoiso D (ap10 FGO X)))%morphism
           = morphism_of G f)
  : F = G.
Proof.
  simple refine (path_functor _ _ _ _).
  - exact FGO.
  - funext X Y f.
    destruct F, G.
    cbn in *.
    induction FGO ; simpl in *.
    specialize (FGM X Y f).
    rewrite left_identity, right_identity in FGM.
    exact FGM.
Defined.

Definition nice_path_functor
           `{Funext}
           {C D : PreCategory}
           {F G : Functor C D}
           (FGO : forall (X : C), F X = G X)
           (FGM : forall {X Y : C} (f : morphism C X Y),
               ((@morphism_isomorphic _ _ _ (Category.Morphisms.idtoiso D (FGO Y)))
                  o (morphism_of F f)
                  o morphism_inverse (Category.Morphisms.idtoiso D (FGO X)))%morphism
               = morphism_of G f)
  : F = G.
Proof.
  simple refine (nice_path_functor' (path_forall _ _ FGO) _).
  intros X Y f.
  rewrite !ap10_path_forall.
  apply FGM.
Defined.