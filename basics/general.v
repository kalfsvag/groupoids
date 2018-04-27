Require Import HoTT.

(** The diagonal of a function with two arguments. *)
Definition diag2
           {X Z : Type}
           (f : X -> X -> Z)
  : X -> Z
  := fun x => f x x.

(** `ap` on the diagonal of a function. *)
Definition ap_diag2
           {X Z : Type}
           (f : X -> X -> Z)
           {x₁ x₂ : X}
           (p : x₁ = x₂)
  : ap (diag2 f) p = ap (fun z => f x₁ z) p @ ap (fun z => f z x₂) p
  := match p with
     | idpath => idpath
     end.

(** Curries a function on a product. *)
Definition curry
           {X Y Z : Type}
           (f : X * Y -> Z)
  : X -> Y -> Z
  := fun x y => f(x, y).

(** `ap` on an uncurried function. *)
Definition uncurry_ap
           {X Y Z : Type}
           (f : X -> Y -> Z)
           {x₁ x₂ : X} {y₁ y₂ : Y}
           (p : x₁ = x₂) (q : y₁ = y₂)
  : ap (uncurry f) (path_prod' p q)
    =
    ap (fun z => f z y₁) p @ ap (f x₂) q
  := match p, q with
     | idpath, idpath => idpath
     end.

(** `ap` on a curried function. *)
Definition curry_ap
           {X Y Z : Type}
           (f : X * Y -> Z)
           {x₁ x₂ : X * Y}
           (p : x₁ = x₂)
  : ap f p
    =
    (ap (fun z => curry f z (snd x₁)) (ap fst p))
      @ (ap (fun z => curry f (fst x₂) z) (ap snd p))
  := match p with
     | idpath => idpath
     end.

(** `ap` on `λx.(x,y)` with `y` constant. *)
Definition ap_pair_l
           {X Y : Type}
           {x₁ x₂ : X} (y : Y)
           (p : x₁ = x₂)
  : ap (fun x => (x, y)) p = path_prod' p idpath
  := match p with
     | idpath => idpath
     end.

(** `ap` on `λy.(x,y)` with `x` constant. *)
Definition ap_pair_r
           {X Y : Type}
           (x : X) {y₁ y₂ : Y}
           (q : y₁ = y₂)
  : ap (pair x) q = path_prod' idpath q
  := match q with
     | idpath => idpath
     end.

(** Univalence says when two types are equal.
    We can also use this to say when two sets are equal and this is given by `path_hset`.
    We study some properties of `path_hset`.
 *)
Section path_hset_prop.
  Context `{Univalence}.

  (** On the identity map, `path_hset` just gives reflexivity. *)
  Definition path_hset_id {A : hSet} : path_hset (equiv_idmap A) = idpath.
  Proof.
    cbn.
    rewrite concat_1p.
    rewrite (eta_path_universe_uncurried 1).
    rewrite path_sigma_hprop_1.
    reflexivity.
  Qed.

  (** On the inverses of equivalence, `path_hset` gives the inverse path. *)
  Definition path_sigma_hprop_inv
        {A : Type}
        (B : A -> hProp)
        {u v : A}
        (p : u = v)
        (x : B u) (y : B v)
    : @path_sigma_hprop A B _ (v;y) (u;x) p^ = (path_sigma_hprop (u;x) (v;y) p)^.
  Proof.
    induction p ; simpl.
    assert (x = y) as ->.
    { apply path_ishprop. }
    rewrite path_sigma_hprop_1.
    reflexivity.
  Defined.
  
  Definition path_hset_inv
             {A B : hSet}
             (f : Equiv A B)
    : path_hset f^-1 = (path_hset f)^.
  Proof.
    cbn.
    rewrite !concat_1p, !concat_p1.
    rewrite path_universe_V_uncurried.
    rewrite (path_sigma_hprop_inv
               (fun Z => BuildhProp (IsHSet Z))
               (path_universe_uncurried f)).
    rewrite ap_V.
    reflexivity.
  Qed.

  (** On a composition, `path_hset` gives the concatanation. *)
  Definition path_universe_uncurried_transitive
             {A B C : Type}
             (f : Equiv A B) (g : Equiv B C)
    : path_universe_uncurried (transitive_equiv A B C f g)
      =
      path_universe_uncurried f @ path_universe_uncurried g.
  Proof.
    apply path_universe_compose.
  Defined.

  Definition path_sigma_hprop_concat
             {A : Type}
             (B : A -> hProp)
             {u v w : A}
             (p : u = v) (q : v = w)
             (x : B u) (y : B v) (z : B w)
    : @path_sigma_hprop A B _ (u;x) (w;z) (p @ q)
      =
      path_sigma_hprop (u;x) (v;y) p @ path_sigma_hprop (v;y) (w;z) q.
  Proof.
    induction p, q.
    assert(y = x) as ->.
    { apply path_ishprop. }
    assert(z = x) as ->.
    { apply path_ishprop. }
    rewrite !path_sigma_hprop_1.
    reflexivity.
  Qed.
  
  Definition path_hset_comp
             {A B C : hSet}
             (f : Equiv A B) (g : Equiv B C)
    : path_hset (transitive_equiv _ _ _ f g) = path_hset f @ path_hset g.
  Proof.
    cbn.
    rewrite !concat_1p, !concat_p1.
    rewrite path_universe_uncurried_transitive.
    rewrite (path_sigma_hprop_concat
               (fun Z => BuildhProp (IsHSet Z))
               (path_universe_uncurried f)
               (path_universe_uncurried g)
               (istrunc_trunctype_type A)
               (istrunc_trunctype_type B)
               (istrunc_trunctype_type C)).
    rewrite ap_pp.
    reflexivity.
  Qed.

  (** This function says when two paths given by `path_hset` are equal. *)
  Definition path_hset_eq
             {A B : hSet}
             (f : Equiv A B) (g : Equiv A B)
             (fg_eq : equiv_fun f == equiv_fun g)
    : path_hset f = path_hset g.
  Proof.
    refine (ap path_hset _).
    rewrite <- (eisretr (issig_equiv A B) f).
    rewrite <- (eisretr (issig_equiv A B) g).
    apply (ap (issig_equiv A B)).
    cbn.
    apply path_sigma_hprop.
    exact (path_forall _ _ fg_eq).
  Qed.
End path_hset_prop.

(** The analogue of `transport_idmap_ap` for `hSets. *)
Definition transport_idmap_ap_set
           {A : Type}
           (P : A -> hSet)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           (u : P a₁)
  : transport P p u = transport (idmap : hSet -> hSet) (ap P p) u
  := match p with
     | idpath => idpath
     end.

(** This computes `transport idmap` (on types) to `transport idmap` (on `hSet`). *)
Definition transport_hpath_to_transport_idmap
           {B C : Type}
           {BS : IsHSet B} {CS : IsHSet C}
           (p : B = C)
           (u : B)
           `{Univalence}
  : transport (idmap : hSet -> hSet)
              (ap (fun u0 : {X : Type & IsHSet X} => @BuildhSet u0.1 u0.2)
                  (path_sigma_hprop (B;BS) (C;CS) p))
              u
    = transport idmap p u.
Proof.
  induction p ; cbn.
  assert(CS = BS) as ->.
  { apply path_ishprop. }
  unfold path_sigma_hprop, path_sigma_uncurried.
  cbn.
  induction (center _).
  reflexivity.
Defined.

(** The analogue of `transport_path_universe` for `hSet`. *) 
Definition transport_path_hset
           {B C : hSet}
           (f : Equiv B C)
           (u : B)
           `{Univalence}
  : transport (idmap : hSet -> hSet) (path_hset f) u
    =
    f u.
Proof.
  cbn.
  rewrite concat_1p, concat_p1.
  rewrite transport_hpath_to_transport_idmap.
  apply transport_path_universe_uncurried.
Defined.

(** Next we prove the truncation of a production is equivalent to the product of truncations. *)
Definition Trunc_prod
           {A B : Type}
           (n : trunc_index)
  : Trunc n A * Trunc n B -> Trunc n (A * B).
Proof.
  intros x.
  simple refine (Trunc_rec _ (fst x)) ; intros y₁.
  simple refine (Trunc_rec _ (snd x)) ; intros y₂.
  exact (tr(y₁,y₂)).
Defined.

Definition Trunc_prod_inv
           {A B : Type}
           (n : trunc_index)
  : Trunc n (A * B) -> Trunc n A * Trunc n B.
Proof.
  apply Trunc_rec.
  exact (fun x => (tr (fst x), tr (snd x))).
Defined.

Global Instance Trunc_prod_isequiv
       {A B : Type}
       (n : trunc_index)
  : IsEquiv (@Trunc_prod A B n).
Proof.
  simple refine (isequiv_adjointify _ (Trunc_prod_inv n) _ _) ; unfold Sect.
  - simple refine (Trunc_ind _ _).
    reflexivity.
  - intros [x₁ x₂]. revert x₁.
    simple refine (Trunc_ind _ _) ; intros y₁ ; simpl.
    revert x₂.
    simple refine (Trunc_ind _ _) ; intros y₂ ; simpl.
    reflexivity.
Defined.

(** If the index is at least `0`, then the sum of `n`-types is again an `n`-type. *)
Global Instance Truncated_sum
       {A B : Type}
       (n : trunc_index)
       (H : trunc_index_leq 0 n)
       `{IsTrunc n A} `{IsTrunc n B}
  : IsTrunc n (A + B).
Proof.
  apply trunc_sum' ; try apply _.
  exact (trunc_leq H).
Defined.

(** If the index is at least `0`, then truncation of the sum is equivalent to the sum of the truncations. *)
Definition Trunc_sum
           {A B : Type}
           (n : trunc_index)
  : Trunc n A + Trunc n B -> Trunc n (A + B).
Proof.
  intros [x | x].
  - simple refine (Trunc_rec _ x) ; intros y.
    exact (tr(inl y)).
  - simple refine (Trunc_rec _ x) ; intros y.
    exact (tr(inr y)).
Defined.

Definition Trunc_sum_inv
           {A B : Type}
           (n : trunc_index)
           (H : trunc_index_leq 0 n)
  : Trunc n (A + B) -> Trunc n A + Trunc n B.
Proof.
  simple refine (Trunc_rec _).
  - apply (Truncated_sum n H).
  - intros [x | x].
    + exact (inl (tr x)).
    + exact (inr (tr x)).
Defined.

Global Instance Trunc_sum_isequiv
       {A B : Type}
       (n : trunc_index)
       (H : trunc_index_leq 0 n)
  : IsEquiv (@Trunc_sum A B n).
Proof.
  simple refine (isequiv_adjointify _ (Trunc_sum_inv n H) _ _) ; unfold Sect.
  - simple refine (Trunc_ind _ _).
    intros [a | a] ; reflexivity.
  - intros [x | x] ; revert x ; simple refine (Trunc_ind _ _).
    * intros a.
      pose (@Truncated_sum (Trunc n A) (Trunc n B) n H).
      apply _.
    * reflexivity.
    * intros a.
      pose (@Truncated_sum (Trunc n A) (Trunc n B) n H).
      apply _.
    * reflexivity.
Defined.