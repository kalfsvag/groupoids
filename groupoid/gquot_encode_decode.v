Require Import HoTT.
From GR Require Import groupoid_quotient path_over globe_over general square.


(** * Encode-decode method for characterizing the path space of [gquot G]. *)
Section encode_decode.
  Variable (A : Type)
           (G : groupoid A).
  Context `{Univalence}.

  (** First, we shall lift the hom set of [G] to a set relation of [gquot G].
      For that, we need an equivalence between [hom G a₁ b] and [hom G a₂ b] (given a morphism [hom G a₁ a₂]),
      and another one between [hom G a b₁] and [hom G a b₂] (given a morphism [hom G b₁ b₂]).
      Those are the [left_action] and the [right_action], resp.
   *)
  Definition right_action
        {a₁ a₂ : A} (b : A)
        (g : hom G a₁ a₂)
    : hom G a₁ b -> hom G a₂ b
    := fun h => (inv g) × h.

  Definition right_action_inv
             {a₁ a₂ : A} (b : A)
             (g : hom G a₁ a₂)
    : hom G a₂ b -> hom G a₁ b
    := fun h => g × h.

  Global Instance right_action_equiv (a : A) {b₁ b₂ : A} (g : hom G b₁ b₂)
    : IsEquiv (right_action a g).
  Proof.
    simple refine (isequiv_adjointify _ (right_action_inv a g) _ _).
    - intros h ; compute.
      refine (ca _ _ _ @ _).
      exact (ap (fun z => z × h) (ic _) @ ec _).
    - intros h ; compute.
      refine (ca _ _ _ @ _).
      exact (ap (fun z => z × h) (ci _) @ ec _).
  Defined.

  Definition left_action
        (a : A) {b₁ b₂ : A}
        (g : hom G b₁ b₂)
    : hom G a b₁ -> hom G a b₂
    := fun h => h × g.

  Definition left_action_inv
             (a : A) {b₁ b₂ : A}
             (g : hom G b₁ b₂)
    : hom G a b₂ -> hom G a b₁
    := fun h => h × (inv g).

  Global Instance left_action_equiv (a : A) {b₁ b₂ : A} (g : hom G b₁ b₂)
    : IsEquiv (left_action a g).
  Proof.
    simple refine (isequiv_adjointify _ (left_action_inv a g) _ _).
    - intros h ; compute.
      refine ((ca _ _ _)^ @ _).
      exact (ap (fun z => h × z) (ic _) @ ce _).
    - intros h ; compute.
      refine ((ca _ _ _)^ @ _).
      exact (ap (fun z => h × z) (ci _) @ ce _).
  Defined.

  (** The action of the unit element is the identity. *)
  Definition left_action_e (a b : A)
    : left_action a (e b) = idmap.
  Proof.
    funext x ; compute.
    apply ce.
  Defined.

  Definition right_action_e (a b : A) :
    right_action b (e a) == idmap.
  Proof.
    intro x.
    unfold right_action.
    rewrite inv_e.
    apply ec.
  Qed.

  (** The lift of [hom G] to [gquot G]. *)
  Definition g_fam : gquot G -> gquot G -> hSet.
  Proof.
    simple refine (gquot_relation A A G G
                          (hom G)
                          (fun _ _ b g => right_action b g)
                          (fun a _ _ g => left_action a g)
                          _ _ _ _ _ _ _
          ).
    - intros a b ; simpl.
      apply right_action_e.
    - intros a b₁ b₂ g x ; unfold right_action ; simpl.
        by rewrite inv_involutive.
    - compute ; intros.
        by rewrite inv_prod, ca.
    - intros ; compute.
      apply ce.
    - intros ; compute.
      reflexivity.
    - compute ; intros.
      apply ca.
    - compute ; intros.
      apply ca.
  Defined.

  (** The computation rules of [g_fam] for the paths. *)
  Definition gquot_fam_l_gcleq
             {a₁ a₂ : A} (b : A) (g : hom G a₁ a₂)
    : ap (fun z => g_fam z (gcl G b)) (gcleq G g)
      =
      path_hset (BuildEquiv _ _ (right_action b g) _)
    := gquot_relation_beta_l_gcleq A A G G (hom G) _ _ _ _ _ _ _ _ _ _ g.

  Definition gquot_fam_r_gcleq
             (a : A) {b₁ b₂ : A} (g : hom G b₁ b₂)
    : ap (g_fam (gcl G a)) (gcleq G g)
      =
      path_hset (BuildEquiv _ _ (left_action a g) _)
    := gquot_relation_beta_r_gcleq A A G G (hom G) _ _ _ _ _ _ _ _ _ _ g.

  Local Instance g_fam_hset x y : IsHSet (g_fam x y)
    := istrunc_trunctype_type _.

  (** The relation [g_fam] is reflexive. *)
  Definition g_fam_refl : forall (x : gquot G), g_fam x x.
  Proof.
    simple refine (gquot_ind_set (fun x => g_fam x x) _ _ _).
    - intros a.
      exact (@e A G a).
    - intros a₁ a₂ g.
      apply path_to_path_over.
      refine (transport_idmap_ap_set (fun x => g_fam x x) (gcleq G g) (e a₁)  @ _).
      refine (ap (fun z => transport _ z _) (_ @ _ @ _) @ _).
      + exact (ap_diag2 g_fam (gcleq G g)).
      + refine (ap (fun z => z @ _) (gquot_fam_r_gcleq a₁ g) @ _).
        exact (ap (fun z => _ @ z) (gquot_fam_l_gcleq a₂ g)).
      + exact (path_hset_comp _ _)^.
      + refine (transport_path_hset _ _ @ _) ; compute.
        refine (ap (fun z => _ × z) (ec _) @ _).
        apply ic.
  Defined.

  (** Now we can define the encode function. *)
  Definition encode_gquot (x y : gquot G) : x = y -> g_fam x y :=
    fun p => transport (g_fam x) p (g_fam_refl x).

  Local Instance g_fam_eq_hset x y : IsHSet (g_fam x y -> x = y).
  Proof.
    apply trunc_forall.
  Defined.

  Opaque g_fam.

  (** We can also define the decode function.
      For this we use double induction over a family of sets.
   *)
  Definition decode_gquot (x y : gquot G) : g_fam x y -> x = y.
  Proof.
    simple refine (gquot_double_ind_set (fun x y => g_fam x y -> x = y) _ _ x y).
    - intros a b g.
      exact (@gcleq A G a b g).
    - intros. simpl.
      simple refine (path_over_arrow _ _ _ _ _ _).
      simpl. intros z.
      apply map_path_over.
      refine (whisker_square idpath (ap_const _ _)^ (ap_idmap _)^ _ _).
      + apply ap.
        refine (_^ @ (transport_idmap_ap_set (g_fam (gcl G a)) (gcleq G g)^ z)^).
        refine (ap (fun p => transport _ p z) (ap_V _ _ @ _) @ _ @ _).
        * exact (ap inverse (gquot_fam_r_gcleq a g)).
        * refine (ap (fun p => transport _ p z) _).
          exact ((path_hset_inv (BuildEquiv _ _ (left_action a g) (left_action_equiv a g)))^).
        * apply transport_path_hset.
      + simpl. apply path_to_square.
        refine (concat_1p _ @ _ @ gconcat _ _ _).
        apply ap. unfold left_action_inv.
        refine ((ce _)^ @ _ @ ca _ _ _).
        refine (ap _ _)^.
        apply ic. 
    - intros. simpl.
      simple refine (path_over_arrow _ _ _ _ _ _).
      simpl. intros z.
      apply map_path_over.
      refine (whisker_square idpath (ap_idmap _)^ (ap_const _ _)^ _ _).
      + apply ap.
        refine (_^ @ (transport_idmap_ap_set (fun z => g_fam z (gcl G b)) (gcleq G g)^ z)^).
        refine (ap (fun p => transport _ p z) (_ @ _) @ _).
        * refine (ap_V (fun z : gquot G => g_fam z (gcl G b)) (gcleq G g) @ _).
          exact (ap inverse (gquot_fam_l_gcleq b g)).
        * exact ((path_hset_inv (BuildEquiv _ _ (right_action b g) (right_action_equiv b g)))^).
        * apply transport_path_hset.
      + simpl. apply path_to_square.
        unfold right_action_inv.       
        exact ((gconcat _ _ _)^ @ (concat_p1 _)^).
  Defined.

  (** The encode and decode maps are inverses of each other. *)
  Definition decode_gquot_encode_gquot
             {x y : gquot G}
             (p : x = y)
    : decode_gquot x y (encode_gquot x y p) = p.
  Proof.
    induction p.
    revert x.
    simple refine (gquot_ind_prop _ _ _).
    intros a ; simpl.
    exact (ge _ _).
  Defined.

  Local Instance encode_gquot_decode_gquot_set (x y : gquot G)
    : IsHProp (forall (p : g_fam x y), encode_gquot x y (decode_gquot x y p) = p).
  Proof.
    apply _.
  Defined.
  
  Definition encode_gquot_decode_gquot
    : forall {x y : gquot G} (p : g_fam x y), encode_gquot x y (decode_gquot x y p) = p.
  Proof.
    simple refine (gquot_double_ind_prop _ _ _).
    intros a b g.
    unfold encode_gquot, g_fam_refl.
    simpl.
    refine (transport_idmap_ap_set (fun x : gquot G => g_fam (gcl G a) x)
                                   (gcleq G g)
                                   (e a) @ _).
    refine (ap (fun p => transport _ p (e a)) (gquot_fam_r_gcleq a _) @ _).
    refine (transport_path_hset _ _ @ _).
    compute.
    exact (ec g).
  Defined.

  Global Instance encode_gquot_isequiv
    : forall {x y: gquot G}, IsEquiv (encode_gquot x y).
  Proof.
    intros x y.
    simple refine (isequiv_adjointify _ (decode_gquot x y) _ _).
    - intros z.
      apply encode_gquot_decode_gquot.
    - intros z.
      apply decode_gquot_encode_gquot.
  Defined.
End encode_decode.
