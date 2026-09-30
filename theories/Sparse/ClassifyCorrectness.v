Require Export Sparse.ClassifyProperties.
Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Reals.Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
Open Scope R_scope.

(* 同じ x 上の具体的な分類単調性から、異なる領域の上下順序を逆に読む。 *)
Lemma classified_vertical_order :
  forall l sub r p q,
    fst p = fst q ->
    region_above (classify l sub r p) (classify l sub r q) ->
    snd q < snd p.
Proof.
  intros l sub r p q Hx Habove.
  destruct (total_order_T (snd q) (snd p)) as [[Hlt | Heq] | Hgt].
  - exact Hlt.
  - exfalso. apply (region_above_not_reverse _ _ Habove).
    left. f_equal. destruct p as [xp yp], q as [xq yq].
    simpl in Hx, Heq |- *. f_equal; lra.
  - exfalso. apply (region_above_not_reverse _ _ Habove).
    eapply classify_vertical_order; eauto.
Qed.

Lemma shift_preserves_strict_vertical_order :
  forall h p q gp gq,
    0 < h ->
    snd p < snd q ->
    region_at_or_above gq gp ->
    snd (shift h gp p) < snd (shift h gq q).
Proof.
  intros h [xp yp] [xq yq] gp gq Hh Hy [Heq | Habove].
  - subst gq. destruct gp; simpl in Hy |- *; lra.
  - destruct Habove; simpl in Hy |- *; lra.
Qed.

Lemma shift_preserves_vertical_order :
  forall h p q gp gq,
    0 < h ->
    snd p <= snd q ->
    region_at_or_above gq gp ->
    snd (shift h gp p) <= snd (shift h gq q).
Proof.
  intros h [xp yp] [xq yq] gp gq Hh Hy [Heq | Habove].
  - subst gq. destruct gp; simpl in Hy |- *; lra.
  - destruct Habove; simpl in Hy |- *; lra.
Qed.

(* Up 以外の分類は、非負の高さで点を上昇させない。 *)
Lemma shift_not_up_nonincreasing :
  forall h g p,
    0 <= h ->
    g <> RegUp ->
    snd (shift h g p) <= snd p.
Proof.
  intros h g [x y] Hh Hnot.
  destruct g; simpl; try lra; contradiction.
Qed.

Definition operate_point
  (l sub r : list Segment) (h : R) (p : Point) : Point :=
  shift h (classify l sub r p) p.

Lemma shift_fst :
  forall h g p, fst (shift h g p) = fst p.
Proof. intros h g p. destruct g; reflexivity. Qed.

Lemma operate_point_fst :
  forall l sub r h p, fst (operate_point l sub r h p) = fst p.
Proof. intros. unfold operate_point. apply shift_fst. Qed.

(* 同じ x 上の分類単調性により、正の高さの上下移動は平面上で単射となる。 *)
Lemma operate_point_injective :
  forall l sub r h p q,
    0 < h ->
    operate_point l sub r h p = operate_point l sub r h q ->
    p = q.
Proof.
  intros l sub r h [xp yp] [xq yq]
    Hh Heq.
  destruct (classify l sub r (xp, yp)) eqn:Hrp;
  destruct (classify l sub r (xq, yq)) eqn:Hrq;
  unfold operate_point, shift in Heq; rewrite Hrp, Hrq in Heq;
  pose proof (f_equal fst Heq) as Hx;
  pose proof (f_equal snd Heq) as Hy; simpl in Hx, Hy.
  - f_equal; lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xq, yq) (xp, yp)
                  ltac:(symmetry; exact Hx)
                  ltac:(rewrite Hrq, Hrp; constructor)) as Horder.
    simpl in Horder. lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xp, yp) (xq, yq)
                  ltac:(exact Hx)
                  ltac:(rewrite Hrp, Hrq; constructor)) as Horder.
    simpl in Horder. lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xp, yp) (xq, yq)
                  ltac:(exact Hx)
                  ltac:(rewrite Hrp, Hrq; constructor)) as Horder.
    simpl in Horder. lra.
  - f_equal; lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xp, yp) (xq, yq)
                  ltac:(exact Hx)
                  ltac:(rewrite Hrp, Hrq; constructor)) as Horder.
    simpl in Horder. lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xq, yq) (xp, yp)
                  ltac:(symmetry; exact Hx)
                  ltac:(rewrite Hrq, Hrp; constructor)) as Horder.
    simpl in Horder. lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xq, yq) (xp, yp)
                  ltac:(symmetry; exact Hx)
                  ltac:(rewrite Hrq, Hrp; constructor)) as Horder.
    simpl in Horder. lra.
  - f_equal; lra.
Qed.

Lemma operate_point_RegFix :
  forall l sub r h p,
    classify l sub r p = RegFix ->
    operate_point l sub r h p = p.
Proof.
  intros l sub r h p H. unfold operate_point. now rewrite H.
Qed.

Lemma classify_sub_endpoint :
  forall l sub r p,
    ClassificationSpec l sub r ->
    endpoint_of sub p ->
    classify l sub r p = RegFix.
Proof.
  intros l sub r p Hspec Hend.
  exact (classified_sub_fixed
           l sub r
           Hspec
           p (endpoint_of_onSegmentlist sub p Hend)).
Qed.

Lemma operate_sub_endpoint :
  forall l sub r h p,
    ClassificationSpec l sub r ->
    endpoint_of sub p ->
    operate_point l sub r h p = p.
Proof.
  intros l sub r h p Hspec Hend.
  apply operate_point_RegFix.
  now apply (classify_sub_endpoint l sub r p Hspec Hend).
Qed.

(* prepared 幾何から、具体的な patch 分類が全域 sparse 再接続に必要な
   仕様をすべて満たすこと。Correctness 層の唯一の外部仮定である。 *)
Lemma classify_spec :
  forall l sub r,
    PreparedGeometry l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    ClassificationSpec l sub r.
Proof.
  intros l sub r Hgeometry Hsparse [ds Hembed] Hext.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { now apply (embed_listDir_connected ds (l ++ sub ++ r)). }
  constructor.
  - now apply classified_sub_fixed_from_construction.
  - now apply classified_segment_endpoints_monotone_from_construction.
  - now apply classified_segment_at_sub_x_from_construction.
  - now apply classified_head_extension_at_sub_x_from_construction.
  - now apply classified_last_extension_at_sub_x_from_construction.
  - now apply classified_head_last_extension_order_from_construction.
  - now apply classified_head_segment_crossing_order_from_construction.
  - now apply classified_last_segment_crossing_order_from_construction.
  - now apply classified_head_slope_case_from_construction.
  - now apply classified_last_slope_case_from_construction.
  - intros Hterminal Hinitial.
    now apply classified_nonadjacent_endpoint_order_no_lid_from_construction.
  - intros h Hh Hl.
    eapply classified_head_init_slope_reconnectable_from_construction; eauto.
  - intros h Hh Hr.
    eapply classified_last_term_slope_reconnectable_from_construction; eauto.
Qed.
