Require Export Sparse.ClassifySpec.
From Stdlib Require Import Lra Psatz.
Import ListNotations.

Lemma ordered_scale_classifier : forall h k seg,
  0 <= h -> endpoint_displacements_ordered k seg ->
  endpoint_displacements_ordered (scale_classifier h k) seg.
Proof.
  intros. unfold endpoint_displacements_ordered, low_value, high_value, scale_classifier in *.
  destruct (V_of (primitive_segment seg)); simpl in *; nra.
Qed.

(* S1 により、直接変位を加えても端点の x/y の向きは変わらない。 *)
Lemma moved_endpoint_axis_orders : forall k seg,
  endpoint_displacements_ordered k seg ->
  (fst (init seg) < fst (term seg) <->
     fst (move_point k (init seg)) < fst (move_point k (term seg))) /\
  (snd (init seg) < snd (term seg) <->
     snd (move_point k (init seg)) < snd (move_point k (term seg))).
Proof.
  intros k seg Horder. split; [reflexivity |].
  pose proof (primitive_segment_embed seg) as He.
  destruct (primitive_segment seg) as [[v h] c] eqn:E.
  unfold endpoint_displacements_ordered, low_value, high_value in Horder.
  rewrite E in Horder. destruct v; simpl in Horder.
  - pose proof (n_end_relation seg h c He).
    unfold move_point; simpl. split; intros; lra.
  - pose proof (s_end_relation seg h c He).
    unfold move_point; simpl. split; intros; lra.
Qed.

Lemma moved_endpoints_reconnectable : forall k seg,
  endpoint_displacements_ordered k seg ->
  reconnectable (move_point k (init seg)) (move_point k (term seg)) (orn_seg seg).
Proof.
  intros k seg Horder.
  pose proof (primitive_segment_embed seg) as He.
  destruct (primitive_segment seg) as [[v h] c] eqn:E.
  unfold endpoint_displacements_ordered, low_value, high_value in Horder.
  rewrite E in Horder. unfold reconnectable, move_point; simpl.
  split.
  - apply neq_init_term_x.
  - destruct v; simpl in Horder.
    + pose proof (n_end_relation seg h c He). lra.
    + pose proof (s_end_relation seg h c He). lra.
Qed.

Lemma sub_displacements_zero : forall l sub r k seg,
  ClassificationSpec l sub r k -> In seg sub ->
  k (init seg) = 0 /\ k (term seg) = 0.
Proof.
  intros l sub r k seg Hspec Hin. split;
    apply (classified_sub_fixed _ _ _ _ Hspec);
    exists seg; split; auto using onInit, onTerm.
Qed.

Lemma sub_boundary_values_zero : forall l sub r k seg x,
  ClassificationSpec l sub r k -> In seg sub ->
  lower_displacement k seg x = 0 /\ upper_displacement k seg x = 0.
Proof.
  intros l sub r k seg x Hspec Hin.
  destruct (sub_displacements_zero _ _ _ _ _ Hspec Hin) as [Hi Ht].
  unfold lower_displacement, upper_displacement, lower_value, upper_value,
    chord_value, low_value, high_value.
  rewrite Hi, Ht.
  destruct (C_of (primitive_segment seg)), (V_of (primitive_segment seg)); simpl; split; ring.
Qed.

(* A1 と S0--S7 を同時に満たす証人の選択。PDF 第6節の未証明部分。
   任意の既存の Prepared 証人に分類器が存在する、とは仮定しない。 *)
Lemma prepared_classification_exists : forall ds1 sub_ds ds2,
  AdmissibleDirs (ds1 ++ sub_ds ++ ds2) ->
  (exists l sub r, PreparedSparseEmbedding ds1 sub_ds ds2 l sub r) ->
  exists l sub r k,
    PreparedSparseEmbedding ds1 sub_ds ds2 l sub r /\
    ClassificationSpec l sub r k.
Admitted.
