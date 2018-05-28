(** This file defines a groupoid quotient HIT and derives some recursion/induction principles for it. *)
Require Import HoTT.
From GR Require Import
     general.
From GR.basics Require Export
     globe_over path_over square.
From GR.groupoid.grpd_bicategory Require Import
     grpd_bicategory.

(** * The groupoid quotient over a type. *)
(** Given a type [A] and a groupoid [G], we construct a type [gquot G] such that
    we have [A -> gquot A G] and the equality of [gquot A G] is described by [G].
    We use the standard method to define the HIT
    <<
    HIT gquot G :=
     | gcl : A -> gquot G
     | gcleq : Π(a₁ a₂ : A), hom G a₁ a₂ -> gcl a₁ = gcl a₂
     | ge : Π(a : A), gcleq (e a) = idpath
     | ginv : Π(a₁ a₂ : A) (g : hom G a₁ a₂), gcleq g⁻¹ = (gcleq g)^
     | gconcat : Π(a₁ a₂ a₃ : A) (g₁ : hom G a₁ a₂) (g₂ : hom G a₂ a₃),
               gcleq (g₁ × g₂) = gcleq g₁ @ gcleq g₂
     | gtrunc : Is-1-Type (gquot G)
    >>
*)
Module Export gquot.
  Private Inductive gquot (G : groupoid) :=
  | gcl : under G -> gquot G.

  Axiom gcleq
    : forall (G : groupoid) {a₁ a₂ : under G} (g : hom G a₁ a₂),
      gcl G a₁ = gcl G a₂.

  Axiom ge
    : forall (G : groupoid) (a : under G),
      gcleq G (e a) = idpath.

  Axiom ginv
    : forall (G : groupoid) {a₁ a₂ : under G} (g : hom G a₁ a₂),
      gcleq G (inv g) = (gcleq G g)^.

  Axiom gconcat
    : forall (G : groupoid)
             {a₁ a₂ a₃ : under G}
             (g₁ : hom G a₁ a₂) (g₂ : hom G a₂ a₃),
      gcleq G (g₁ · g₂) = gcleq G g₁ @ gcleq G g₂.
  
  Axiom gtrunc
    : forall (G : groupoid), IsTrunc 1 (gquot G).

  Section gquot_ind.
    Variable (G : groupoid)
             (Y : gquot G -> Type)
             (gclY : forall (a : under G), Y(gcl G a))
             (gcleqY : forall (a₁ a₂ : under G) (g : hom G a₁ a₂),
                 path_over Y (gcleq G g) (gclY a₁) (gclY a₂))
             (geY : forall (a : under G), globe_over Y
                                                (path_to_globe (ge G a))
                                                (gcleqY a a (e a))
                                                (path_over_id (gclY a)))
             (ginvY : forall (a₁ a₂ : under G) (g : hom G a₁ a₂),
                 globe_over Y
                            (path_to_globe (ginv G g))
                            (gcleqY a₂ a₁ (inv g))
                            (path_over_inv (gcleqY a₁ a₂ g)))
             (gconcatY : forall (a₁ a₂ a₃ : under G)
                                (g₁ : hom G a₁ a₂) (g₂ : hom G a₂ a₃),
                 globe_over Y
                            (path_to_globe (gconcat G g₁ g₂))
                            (gcleqY a₁ a₃ (g₁ · g₂))
                            (path_over_concat (gcleqY a₁ a₂ g₁)
                                              (gcleqY a₂ a₃ g₂)))
             (truncY : forall (x : gquot G), IsTrunc 1 (Y x)).

    Fixpoint gquot_ind (g : gquot G) : Y g
      := (match g with
         | gcl a => fun _ _ _ _ _ => gclY a
          end) gcleqY geY ginvY gconcatY truncY.

    Axiom gquot_ind_beta_gcleq : forall (a₁ a₂ : under G) (g : hom G a₁ a₂),
        apd_po gquot_ind (gcleq G g)
        =
        gcleqY a₁ a₂ g.
  End gquot_ind.
End gquot.

Arguments gquot_ind {G} Y gclY gcleqY geY ginvY gconcatY truncY.