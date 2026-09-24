Require Export Sparse.SegmentListGeometry.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lra.

(* sub の分割条件と、端点を上下移動するための十分大きな高さ。 *)
Definition well_split (l sub r : list Segment) : Prop :=
  sub <> [] /\ x_monotone_segs sub /\ ~ close (l ++ sub ++ r).

Definition h_large (h : R) (sub : list Segment) : Prop :=
  0 < h /\ rect_height (bbox_of sub) < h.

Lemma choose_h : forall sub, exists h, h_large h sub.
Proof.
  intros sub. exists (Rmax 1 (rect_height (bbox_of sub) + 1)).
  unfold h_large. split.
  - eapply Rlt_le_trans; [apply Rlt_0_1 | apply Rmax_l].
  - eapply Rlt_le_trans; [| apply Rmax_r]. lra.
Qed.
