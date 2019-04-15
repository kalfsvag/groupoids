Require Import HoTT.
From GR.basics Require Import
     general.
From GR Require Export
     (* groupoid.grpd_bicategory.grpd_bicategory *)
     (* groupoid.grpd_bicategory.sum_grpd *)
     (* groupoid.grpd_bicategory.prod_grpd *)
     (* groupoid.grpd_bicategory.grpd_laws *)
     (* groupoid.groupoid_quotient.gquot_principles *)
     basics.polynomial.
Require Import cquot.
Require Import cquot_principles.
(* Require Import Datatypes. *)
From HoTT.Categories Require Import
     Category.


(** * Groupoid quotient commmutes with polynomials *)

(** ** The groupoid quotient commutes with sums.
    We use recursion to define the maps and `gquot_ind_set` to prove they are inverses.
 *)
Section cquot_sum.
  Variable (C₁ C₂ : PreCategory).

  Definition cquot_sum_in
             (z : cquot C₁ + cquot C₂)
    : cquot (sum C₁ C₂).
  Proof.
    destruct z as [x | y].
    - exact (cquot_rec
               _
               (fun a => ccl (sum C₁ C₂) (inl a))
               (fun a₁ a₂ c => @ccleq (sum C₁ C₂) (inl a₁) (inl a₂) c)
               (fun a => ce (sum C₁ C₂) (inl a))
               (fun a₁ a₂ a₃ c₁ c₂ =>
                  @cconcat (sum C₁ C₂)
                           (inl a₁)
                           (inl a₂)
                           (inl a₃)
                           c₁
                           c₂)
               x).
    - exact (cquot_rec
               _
               (fun b => ccl (sum C₁ C₂) (inr b))
               (fun b₁ b₂ c => @ccleq (sum C₁ C₂) (inr b₁) (inr b₂) c)
               (fun b => ce (sum C₁ C₂) (inr b))
               (fun b₁ b₂ b₃ c₁ c₂ =>
                  @cconcat (sum C₁ C₂)
                           (inr b₁)
                           (inr b₂)
                           (inr b₃)
                           c₁
                           c₂)
               y).
  Defined.

  Definition cquot_sum_out : cquot (sum C₁ C₂) -> cquot C₁ + cquot C₂.
  Proof.
    simple refine (cquot_rec _ _ _ _ _) ; cbn.
    - intros [a | b].
      + exact (inl (ccl _ a)).
      + exact (inr (ccl _ b)).
    - intros [a₁ | b₁] [a₂ | b₂] c ; try refine (Empty_rec c).
      + exact (ap inl (ccleq _ c)).
      + exact (ap inr (ccleq _ c)).
    - intros [a | b].
      + exact (ap _ (ce _ a)).
      + exact (ap _ (ce _ b)).
    - intros [a₁ | b₁] [a₂ | b₂] [a₃ | b₃] c₁ c₂;
        try (exact (Empty_rec c₁) || exact (Empty_rec c₂)).
      + exact (ap (ap inl) (cconcat C₁ c₁ c₂) @ ap_pp _ _ _).
      + exact (ap (ap inr) (cconcat C₂ c₁ c₂) @ ap_pp _ _ _).
  Defined.

  Lemma cquot_sum_out_in_sect : Sect cquot_sum_out cquot_sum_in.
  Proof.
    intros x.
    simple refine (cquot_ind_set (fun x => cquot_sum_in (cquot_sum_out x) = x) _ _ _ x).
    - intros [ | ] ; reflexivity.
    - intros [a1 | b1] [a2 | b2] c ; try refine (Empty_rec c) ; simpl in c.
      (**
       <<
                     1
       [inl(a₂)] —————————→ [inl(a₂)]
          |                     |
          |                     |
 ap       |                     |
  (cquot_sum_in o               | ap 1 [c]
    cquot_sum_out) [c]          |
          |                     |
          |                     |
          |                     |
       [inl(a₁)] —————————→ [inl(a₁)]
                     1
       >>
       *)
      + apply map_path_over.
        refine (whisker_square idpath _ (ap_idmap _)^ idpath (vrefl _)).
        refine (_ @ (ap_compose _ _ _)^).
        refine ((ap _ _ @ _)^).
        ** apply cquot_rec_beta_ccleq.
        ** refine ((ap_compose inl cquot_sum_in _)^ @ _).
           apply cquot_rec_beta_ccleq.
      + apply map_path_over.
        refine (whisker_square idpath _ (ap_idmap _)^ idpath (vrefl _)).
        refine (_ @ (ap_compose _ _ _)^).
        refine ((ap _ _ @ _ )^).
        ** apply cquot_rec_beta_ccleq.
        ** refine ((ap_compose inr cquot_sum_in _)^ @ _).
           apply cquot_rec_beta_ccleq.
  Qed.

  Lemma cquot_sum_in_out_sect : Sect cquot_sum_in cquot_sum_out.
  Proof.
    intros [x | y].
    - simple refine (cquot_ind_set
                       (fun z => cquot_sum_out (cquot_sum_in (inl z)) = inl z) _ _ _ x).
      + exact (fun _ => idpath).
      + intros a₁ a₂ c.
        apply map_path_over.
        refine (whisker_square idpath _ idpath idpath (vrefl _)).
        * refine (_ @ (ap_compose (cquot_sum_in o inl) cquot_sum_out _)^).
          refine (ap _ _ @ _)^.
          ** apply cquot_rec_beta_ccleq.
          ** apply cquot_rec_beta_ccleq.
    - simple refine (cquot_ind_set
                       (fun z => cquot_sum_out (cquot_sum_in (inr z)) = inr z) _ _ _ y).
      + exact (fun _ => idpath).
      + intros a₁ a₂ c.
        apply map_path_over.
        refine (whisker_square idpath _ idpath idpath (vrefl _)).
        refine (_ @ (ap_compose (cquot_sum_in o inr) cquot_sum_out _)^).
        refine (ap _ _ @ _)^.
        ** apply cquot_rec_beta_ccleq.
        ** apply cquot_rec_beta_ccleq.
  Qed.

  Global Instance cquot_sum_in_isequiv : IsEquiv cquot_sum_in
    := isequiv_adjointify _ cquot_sum_out cquot_sum_out_in_sect cquot_sum_in_out_sect.

  Definition cquot_sum : (cquot C₁ + cquot C₂) <~> cquot (sum C₁ C₂) :=
    BuildEquiv _ _ cquot_sum_in _.
End cquot_sum.

(** ** The croupoid quotient commutes with products.
    We use recursion and double recursion to define the maps.
    We use `gquot_ind_set` to show they are inverses.
 *)
Section cquot_prod.
  Variable (C₁ C₂ : PreCategory).

  Context `{Funext}.

  Definition cquot_prod_in
    : cquot C₁ * cquot C₂ -> cquot (prod C₁ C₂).
  Proof.
    simple refine (cquot_double_rec _ _ _ _ _ _ _ _ _).
    - exact (fun a b => ccl (prod C₁ C₂) (a, b)).
    - intros a b₁ b₂ c ; simpl.
      apply ccleq.
      exact (identity a, c).
    - intros a b ; simpl.
      apply ce.
    - intros a b₁ b₂ b₃ c₁ c₂ ; simpl.
      rewrite <- cconcat ; cbn.
      rewrite right_identity.
      reflexivity.
    - intros a₁ a₂ b c ; simpl.
      apply ccleq.
      exact (c, identity b).
    - intros a b ; simpl.
      apply ce.
    - intros a₁ a₂ a₃ b c₁ c₂ ; simpl.
      rewrite <- cconcat ; cbn.
      rewrite right_identity.
      reflexivity.
    - intros a₁ a₂ b₁ b₂ c₁ c₂ ; simpl.
      apply path_to_square.
      rewrite <- !cconcat.
      apply ap ; cbn.
      rewrite !right_identity, !left_identity.
      reflexivity.
  Defined.

  Definition cquot_prod_out : cquot (prod C₁ C₂) -> cquot C₁ * cquot C₂.
  Proof.
    simple refine (cquot_rec _ _ _ _ _) ; cbn.
    - exact (fun x => (ccl _ (fst x), ccl _ (snd x))).
    - intros a₁ a₂ c ; simpl.
      exact (path_prod' (ccleq _ (fst c)) (ccleq _ (snd c))).
    - intros ; simpl.
      refine (ap (fun p => path_prod' p _) (ce _ _) @ _).
      exact (ap (fun p => path_prod' _ p) (ce _ _)).
    - intros ; simpl.
      refine (ap (fun p => path_prod' p _) (cconcat _ _ _) @ _).
      refine (ap (fun p => path_prod' _ p) (cconcat _ _ _) @ _).
      apply path_prod_pp.
  Defined.

  Lemma cquot_prod_out_in_sect : Sect cquot_prod_out cquot_prod_in.
  Proof.
    simple refine (cquot_ind_set (fun x => cquot_prod_in (cquot_prod_out x) = x) _ _ _).
    - reflexivity.
    - intros x₁ x₂ c.
      apply map_path_over.
      refine (whisker_square idpath _ (ap_idmap _)^ idpath (vrefl _)).
      refine ((ap_compose _ _ _ @ ap (ap cquot_prod_in) _ @ _ @ _)^).
      * apply cquot_rec_beta_ccleq.
      * apply cquot_double_rec_beta_ccleq.
      * simpl.
        refine ((@cconcat (prod C₁ C₂)
                          _
                          (fst x₂, snd x₁)
                          _
                          (fst c, identity (snd x₁))
                          (identity (fst x₂), snd c))^
                @ _).
        apply ap.
        exact (path_prod' (left_identity _ _ _ _) (right_identity _ _ _ _)).
  Qed.

  Lemma cquot_prod_in_out_sect : Sect cquot_prod_in cquot_prod_out.
  Proof.
    intros [x₁ x₂].
    revert x₁ x₂.
    simple refine (cquot_double_ind_set _ _ _).
    - reflexivity.
    - intros a b₁ b₂ c.
      apply map_path_over.
      refine (whisker_square idpath _ (ap_pair_r _ _)^ idpath (vrefl _)).
      refine (_ @ _ @ _ @ _)^.
      * exact (ap_compose (fun z => cquot_prod_in (ccl C₁ a,z)) cquot_prod_out (ccleq C₂ c)).
      * apply ap.
        refine (ap_compose _ _ _ @ _).
        apply cquot_double_rec_beta_r_ccleq.
      * exact (cquot_rec_beta_ccleq (prod C₁ C₂)
                                    _ _ _ _ _ _
                                    (a, b₁) (a, b₂) (identity a, c)).
      * exact (ap (fun z => path_prod' z (ccleq C₂ c)) (ce C₁ a)).
    - intros a₁ a₂ b c.
      apply map_path_over.
      refine (whisker_square idpath _ (ap_pair_l _ _)^ idpath (vrefl _)).
      refine (_ @ _ @ _ @ _)^.
      * exact (ap_compose (fun z => cquot_prod_in (z,ccl C₂ b)) cquot_prod_out (ccleq C₁ c)).
      * apply ap.
        refine (ap_compose _ _ _ @ _).
        apply cquot_double_rec_beta_l_ccleq.
      * exact (cquot_rec_beta_ccleq (prod C₁ C₂)
                                    _ _ _ _ _ _
                                    (a₁, b) (a₂, b) (c, identity b)).
      * exact (ap (path_prod' (ccleq C₁ c)) (ce C₂ b)).
  Qed.

  Global Instance cquot_prod_in_isequiv : IsEquiv cquot_prod_in
    := isequiv_adjointify _ cquot_prod_out cquot_prod_out_in_sect cquot_prod_in_out_sect.

  Definition cquot_prod : (cquot C₁ * cquot C₂) <~> cquot (prod C₁ C₂) :=
    BuildEquiv _ _ cquot_prod_in _.
End cquot_prod.
