Require Import Admissible.
Require Import Reduction.
Require Import Stdlib.Reals.Reals.
Require Import Embed.
Require Import PrimitiveSegment.
Require Import Segment.
Require Import SegmentsTranslation.
Require Import ListExt.
Require Import Stdlib.Logic.ClassicalDescription.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Relations.Operators_Properties.

Require Export Sparse.Sparsity.

(* 端点だけに意味を持つ分類。 *)

Inductive Region : Type := RegFix | RegUp | RegDown.

(* 安全な split が使う、sub に隣接する左側セグメントの単純な x 方向の
   折返し判定。以下の幾何学的な [terminal_lid] とは区別する。 *)
Definition terminal_backtrack_lid (l : list Segment) : Prop :=
  l <> [] /\
  fst (term (last_segment l)) < fst (init (last_segment l)).

Definition initial_backtrack_lid (r : list Segment) : Prop :=
  r <> [] /\
  fst (term (hd_segment r)) < fst (init (hd_segment r)).

Inductive region_above : Region -> Region -> Prop :=
  | RegUp_above_Fix : region_above RegUp RegFix
  | RegUp_above_Down : region_above RegUp RegDown
  | RegFix_above_Down : region_above RegFix RegDown.

Definition region_at_or_above (g1 g2 : Region) : Prop :=
  g1 = g2 \/ region_above g1 g2.

Lemma region_at_or_above_antisym : forall g1 g2,
  region_at_or_above g1 g2 ->
  region_at_or_above g2 g1 ->
  g1 = g2.
Proof.
  intros g1 g2 H12 H21.
  destruct g1, g2; try reflexivity;
    destruct H12 as [H | H]; try discriminate; inversion H;
    destruct H21 as [H' | H']; try discriminate; inversion H'.
Qed.

Lemma region_at_or_above_RegUp_inv : forall g,
  region_at_or_above g RegUp -> g = RegUp.
Proof. intros g [H | H]; [exact H | inversion H]. Qed.

Lemma RegDown_at_or_above_inv : forall g,
  region_at_or_above RegDown g -> g = RegDown.
Proof. intros g [H | H]; [now symmetry | inversion H]. Qed.

Lemma region_above_not_reverse :
  forall g1 g2,
    region_above g1 g2 -> ~ region_at_or_above g2 g1.
Proof.
  intros g1 g2 H. destruct H; intros [Heq | Hrev];
    try discriminate; inversion Hrev.
Qed.

Definition endpoint_of_seg (s : Segment) (p : Point) : Prop :=
  p = init s \/ p = term s.

Definition endpoint_of (ls : list Segment) (p : Point) : Prop :=
  exists s, In s ls /\ endpoint_of_seg s p.

Lemma endpoint_of_onSegmentlist : forall ls p,
  endpoint_of ls p -> onSegmentlist ls p.
Proof.
  intros ls p [s [Hs [-> | ->]]]; exists s; split; auto using onInit, onTerm.
Qed.

Definition in_sub_x_range (sub : list Segment) (p : Point) : Prop :=
  rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub).

Definition above_sub_at_x (sub : list Segment) (p : Point) : Prop :=
  exists q,
    onSegmentlist sub q
    /\ fst p = fst q
    /\ snd q < snd p.

Definition below_sub_at_x (sub : list Segment) (p : Point) : Prop :=
  exists q,
    onSegmentlist sub q
    /\ fst p = fst q
    /\ snd p < snd q.

(* prepared な初期埋め込みで [sub] に要求する局所幾何。内部点を端点長方形の
   開内部に置くことで、両側の蓋を除いた通常再接続でも全域 sparse 性を扱える。 *)
Definition sub_strictly_inside_endpoint_rect (sub : list Segment) : Prop :=
  forall i s p,
    nth_error sub i = Some s ->
    onSegment s p ->
    (i = 0%nat -> p <> init s) ->
    (S i = length sub -> p <> term s) ->
    in_rect (rect_of sub) p.

Definition avoids_sub_vertical_gap (sub : list Segment) (p : Point) : Prop :=
  ~ exists qlo qhi,
      onSegmentlist sub qlo /\ onSegmentlist sub qhi
      /\ fst p = fst qlo /\ fst p = fst qhi
      /\ snd qlo < snd p < snd qhi.

Definition external_points_avoid_sub_vertical_gap
    (l sub r : list Segment) : Prop :=
  forall p,
    onSegmentlist (l ++ r) p ->
    ~ onSegmentlist sub p ->
    avoids_sub_vertical_gap sub p.

(* x 方向の閉区間が交わる二つの端点長方形。 *)
Definition segment_x_ranges_overlap (s t : Segment) : Prop :=
  rx0 (rect_of [s]) <= rx1 (rect_of [t])
  /\ rx0 (rect_of [t]) <= rx1 (rect_of [s]).

(* [sub] の上側に入る外側セグメントと、左右の境界セグメントとの
   配置としての蓋。全域 sparse 性を保存する prepared 埋め込みでは、
   この二種類の蓋を最初から除外する。 *)
Definition segment_meets_upper_sub_rect
    (sub : list Segment) (t : Segment) : Prop :=
  exists p,
    onSegment t p
    /\ in_rect (rect_of sub) p
    /\ above_sub_at_x sub p.

Definition upper_lid_witness
    (l sub r : list Segment) (boundary : Segment) : Prop :=
  exists t,
    In t (l ++ r)
    /\ segment_meets_upper_sub_rect sub t
    /\ segment_x_ranges_overlap boundary t
    /\ ry1 (rect_of [t]) < ry0 (rect_of [boundary]).

Definition terminal_lid (l sub r : list Segment) : Prop :=
  l <> [] /\ upper_lid_witness l sub r (last_segment l).

Definition initial_lid (l sub r : list Segment) : Prop :=
  r <> [] /\ upper_lid_witness l sub r (hd_segment r).

(* x 単調性の代わりに、構成時に選ぶ具体的な埋め込みへ要求する幾何条件。 *)
Record PreparedGeometry (l sub r : list Segment) : Prop := {
  prepared_sub_nonempty : sub <> [];
  prepared_sub_strictly_inside : sub_strictly_inside_endpoint_rect sub;
  prepared_sub_x_order :
    fst (init (hd_segment sub)) < fst (term (last_segment sub));
  prepared_external_no_gap : external_points_avoid_sub_vertical_gap l sub r;
  prepared_no_terminal_lid : ~ terminal_lid l sub r;
  prepared_no_initial_lid : ~ initial_lid l sub r
}.

Lemma segment_has_point_at_x :
  forall seg x,
    rx0 (rect_of [seg]) <= x <= rx1 (rect_of [seg]) ->
    exists p, onSegment seg p /\ fst p = x.
Proof.
  intros seg x Hx.
  destruct (total_order_T (fst (init seg)) (fst (term seg)))
    as [[Hix | Heq] | Htx].
  - change (Rmin (fst (init seg)) (fst (term seg)) <= x <=
            Rmax (fst (init seg)) (fst (term seg))) in Hx.
    rewrite Rmin_left in Hx by lra.
    rewrite Rmax_right in Hx by lra.
    destruct (Rle_dec (snd (init seg)) (snd (term seg))) as [Hy | Hy].
    + destruct (exist_between_x_pos seg
                  (fst (init seg)) (fst (term seg))
                  (snd (init seg)) (snd (term seg)) x
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  Hy (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
    + destruct (exist_between_x_neg seg
                  (fst (init seg)) (fst (term seg))
                  (snd (init seg)) (snd (term seg)) x
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  ltac:(lra) (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
  - exfalso. apply (neq_init_term_x seg).
    unfold init_x, term_x. exact Heq.
  - change (Rmin (fst (init seg)) (fst (term seg)) <= x <=
            Rmax (fst (init seg)) (fst (term seg))) in Hx.
    rewrite Rmin_right in Hx by lra.
    rewrite Rmax_left in Hx by lra.
    destruct (Rle_dec (snd (term seg)) (snd (init seg))) as [Hy | Hy].
    + destruct (exist_between_x_pos seg
                  (fst (term seg)) (fst (init seg))
                  (snd (term seg)) (snd (init seg)) x
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  Hy (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
    + destruct (exist_between_x_neg seg
                  (fst (term seg)) (fst (init seg))
                  (snd (term seg)) (snd (init seg)) x
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  ltac:(lra) (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
Qed.

(* 連結した二つの x 区間の和は、両外端を結ぶ区間を覆う。 *)
Lemma x_interval_bridge : forall a b c x,
  Rmin a c <= x <= Rmax a c ->
  Rmin a b <= x <= Rmax a b \/
  Rmin b c <= x <= Rmax b c.
Proof.
  intros a b c x Hx.
  unfold Rmin, Rmax in *.
  repeat destruct Rle_dec; lra.
Qed.

(* x 単調でなくても、連結な列の両端間の各 x には sub 上の点がある。 *)
Lemma connected_sub_has_point_at_x :
  forall sub x,
    sub <> [] ->
    connected sub ->
    rx0 (rect_of sub) <= x <= rx1 (rect_of sub) ->
    exists q, onSegmentlist sub q /\ fst q = x.
Proof.
  intros sub x Hne.
  destruct sub as [|a tail]; [contradiction|].
  clear Hne. revert a x.
  induction tail as [|b tail IH]; intros a x Hconn Hx.
  - destruct (segment_has_point_at_x a x Hx) as [q [Hon Hqx]].
    exists q. split; [exists a; split; [now left | exact Hon] | exact Hqx].
  - assert (Hab : term a = init b).
    { apply (Hconn 0%nat a b); reflexivity. }
    assert (HconnTail : connected (b :: tail)).
    { intros i s1 s2 H1 H2.
      apply (Hconn (S i) s1 s2); simpl; assumption. }
    assert (Hlast :
        last_segment (a :: b :: tail) = last_segment (b :: tail)).
    { change (last_segment ([a] ++ b :: tail) = last_segment (b :: tail)).
      apply last_app_nonnil. discriminate. }
    assert (Hbetween :
        Rmin (fst (init a)) (fst (term (last_segment (b :: tail)))) <= x <=
        Rmax (fst (init a)) (fst (term (last_segment (b :: tail))))).
    { unfold rect_of in Hx. simpl in Hx. rewrite Hlast in Hx.
      exact Hx. }
    destruct (x_interval_bridge
                (fst (init a)) (fst (term a))
                (fst (term (last_segment (b :: tail)))) x Hbetween)
      as [Ha | Htail].
    + destruct (segment_has_point_at_x a x Ha) as [q [Hon Hqx]].
      exists q. split; [exists a; split; [now left | exact Hon] | exact Hqx].
    + assert (HxTail :
        rx0 (rect_of (b :: tail)) <= x <=
        rx1 (rect_of (b :: tail))).
      { unfold rect_of. simpl. rewrite <- Hab. exact Htail. }
      destruct (IH b x HconnTail HxTail) as [q [[s [Hs Hon]] Hqx]].
      exists q. split.
      * exists s. split; [now right | exact Hon].
      * exact Hqx.
Qed.

Definition EndpointClassifier : Type := Point -> Region.

(* 分類された端点を高さ h だけ上下へ動かす。分類仕様でも同じ移動を使う。 *)
Definition shift (h : R) (g : Region) (p : Point) : Point :=
  match g with
  | RegFix  => p
  | RegUp   => (fst p, snd p + h)
  | RegDown => (fst p, snd p - h)
  end.

Definition region_translation (h : R) (g : Region) : Point :=
  match g with
  | RegFix => (0, 0)
  | RegUp => (0, h)
  | RegDown => (0, - h)
  end.

Lemma shift_as_translation :
  forall h g p, shift h g p = translate_pt (region_translation h g) p.
Proof.
  intros h g [x y]. destruct g; unfold shift, region_translation, translate_pt;
    simpl; f_equal; ring.
Qed.

(* 先頭・末尾で本当に必要なのは、領域の形ではなく移動後にも指定した
   側の傾きを保って再接続できることである。 *)
Definition classified_init_slope_reconnectable
    (classifier : EndpointClassifier) (h : R) (seg : Segment) : Prop :=
  reconnect_init_slope
    (shift h (classifier (init seg)) (init seg))
    (shift h (classifier (term seg)) (term seg))
    (orn_seg seg) (slope_init seg).

Definition classified_term_slope_reconnectable
    (classifier : EndpointClassifier) (h : R) (seg : Segment) : Prop :=
  reconnect_term_slope
    (shift h (classifier (init seg)) (init seg))
    (shift h (classifier (term seg)) (term seg))
    (orn_seg seg) (slope_term seg).
