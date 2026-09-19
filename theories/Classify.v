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



Require Export Sparsity.
(* ================================================================= *)
(*  1.  端点の分類と上下移動                                         *)
(* ================================================================= *)

Inductive Region : Type := RegFix | RegUp | RegDown.

Inductive region_above : Region -> Region -> Prop :=
  | RegUp_above_Fix : region_above RegUp RegFix
  | RegUp_above_Down : region_above RegUp RegDown
  | RegFix_above_Down : region_above RegFix RegDown.

Definition region_at_or_above (g1 g2 : Region) : Prop :=
  g1 = g2 \/ region_above g1 g2.

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
  intros ls p [s [Hs Hend]]. exists s. split; [exact Hs |].
  destruct Hend as [Hp | Hp].
  - subst p. apply onInit.
  - subst p. apply onTerm.
Qed.

(* 分類は曲線全体の配置を見て選ぶ。sub 上の端点は固定し、全体の先頭と
   末尾では延長線の傾きを平行移動で保てる配置を要求する。 *)
Parameter classify :
  list Segment -> list Segment -> list Segment -> Point -> Region.

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

(* x 方向だけでは分離されていない二つの端点長方形。 *)
Definition segment_x_ranges_overlap (s t : Segment) : Prop :=
  rx0 (rect_of [s]) < rx1 (rect_of [t])
  /\ rx0 (rect_of [t]) < rx1 (rect_of [s]).

Record ClassificationSpec (l sub r : list Segment) : Prop := {

  (* sub は固定 *)
  classified_sub_fixed :
    forall p, onSegmentlist sub p -> classify l sub r p = RegFix;

  (* セグメントの始点が終点より低く，始点の領域が Up なら終点も Up など *)
  classified_segment_endpoints_monotone :
    forall s,
      In s (l ++ sub ++ r) ->
      (snd (init s) < snd (term s) ->
        region_at_or_above (classify l sub r (term s)) (classify l sub r (init s)))
      /\
      (snd (term s) < snd (init s) ->
        region_at_or_above (classify l sub r (init s)) (classify l sub r (term s)));

  (* ある点が Up なら，それより上の点も Up など *)
  classified_same_x_monotone :
    forall p q,
      fst p = fst q ->
      snd p < snd q ->
      region_at_or_above (classify l sub r q) (classify l sub r p);

  (* x 範囲が重なる非隣接セグメントについては，下側の長方形が Up なら上側の長方形も Up など *)
  classified_nonadjacent_endpoint_order :
    forall i j s t ps pt,
      nth_error (l ++ sub ++ r) i = Some s ->
      nth_error (l ++ sub ++ r) j = Some t ->
      (S i < j \/ S j < i)%nat ->
      segment_x_ranges_overlap s t ->
      endpoint_of_seg s ps ->
      endpoint_of_seg t pt ->
      snd ps <= snd pt ->
      region_at_or_above
        (classify l sub r pt) (classify l sub r ps);

  (* sub と同じ x 座標を持つセグメントは Up もしくは Down *)
  classified_segment_at_sub_x :
    forall s p,
      In s (nonadjacent_sides l r) ->
      onSegment s p ->
      in_sub_x_range sub p ->
      (above_sub_at_x sub p ->
         classify l sub r (init s) = RegUp
         /\ classify l sub r (term s) = RegUp)
      /\
      (below_sub_at_x sub p ->
         classify l sub r (init s) = RegDown
         /\ classify l sub r (term s) = RegDown);

  (* strict 延長線が sub 長方形の開 x 範囲へ入る場合，
     その延長線を動かす基点は Fix ではない。 *)
  classified_head_extension_at_sub_x :
    forall p,
      onHead_extend_strict (l ++ sub ++ r) p ->
      rx0 (rect_of sub) < fst p < rx1 (rect_of sub) ->
      classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegUp
      \/ classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegDown;

  classified_last_extension_at_sub_x :
    forall p,
      onLast_extend_strict (l ++ sub ++ r) p ->
      rx0 (rect_of sub) < fst p < rx1 (rect_of sub) ->
      classify l sub r (term (last_segment (l ++ sub ++ r))) = RegUp
      \/ classify l sub r (term (last_segment (l ++ sub ++ r))) = RegDown;

  (* 延長線が同じ x 座標の点を持つ時，下側が Up なら上側も Up など *)
  classified_head_last_extension_order :
    forall ph pl,
      onHead_extend (l ++ sub ++ r) ph ->
      onLast_extend (l ++ sub ++ r) pl ->
      fst ph = fst pl ->
      (snd ph < snd pl ->
         region_at_or_above
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
           (classify l sub r (init (hd_segment (l ++ sub ++ r)))))
      /\
      (snd pl < snd ph ->
         region_at_or_above
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
           (classify l sub r (term (last_segment (l ++ sub ++ r)))));

  (* セグメントと延長線が同じ x 座標の点を持つ時，下側が Up なら上側も Up など *)
  classified_head_segment_crossing_order :
    forall s e q,
      In s (l ++ sub ++ r) ->
      onSegment s e ->
      onHead_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      (snd q < snd e ->
         region_at_or_above
           (classify l sub r (init s))
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
         /\ region_at_or_above
           (classify l sub r (term s))
           (classify l sub r (init (hd_segment (l ++ sub ++ r)))))
      /\
      (snd e < snd q ->
         region_at_or_above
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
           (classify l sub r (init s))
         /\ region_at_or_above
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
           (classify l sub r (term s)));

  classified_last_segment_crossing_order :
    forall s e q,
      In s (l ++ sub ++ r) ->
      onSegment s e ->
      onLast_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      (snd q < snd e ->
         region_at_or_above
           (classify l sub r (init s))
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
         /\ region_at_or_above
           (classify l sub r (term s))
           (classify l sub r (term (last_segment (l ++ sub ++ r)))))
      /\
      (snd e < snd q ->
         region_at_or_above
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
           (classify l sub r (init s))
         /\ region_at_or_above
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
           (classify l sub r (term s)));

  (* 先頭の両端が別領域なら、始点傾きを保てる向き・凸性に限る。 *)
  classified_head_slope_case :
    l <> [] ->
    classify l sub r (init (hd_segment l)) =
      classify l sub r (term (hd_segment l))
    \/ (classify l sub r (init (hd_segment l)) = RegUp
        /\ (embed (s, w, cx) (hd_segment l)
            \/ embed (s, e, cx) (hd_segment l)))
    \/ (classify l sub r (init (hd_segment l)) = RegDown
        /\ (embed (n, w, cc) (hd_segment l)
            \/ embed (n, e, cc) (hd_segment l)));

  (* 末尾では双対的に、終点傾きを保てる場合だけ別領域を許す。 *)
  classified_last_slope_case :
    r <> [] ->
    classify l sub r (init (last_segment r)) =
      classify l sub r (term (last_segment r))
    \/ (classify l sub r (term (last_segment r)) = RegUp
        /\ (embed (n, w, cx) (last_segment r)
            \/ embed (n, e, cx) (last_segment r)))
    \/ (classify l sub r (term (last_segment r)) = RegDown
        /\ (embed (s, w, cc) (last_segment r)
            \/ embed (s, e, cc) (last_segment r)))
}.

Axiom classify_spec :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    ClassificationSpec l sub r.

(* 同じ x 上の分類単調性から、異なる領域の点の上下順序を逆に読む。 *)
Lemma classified_vertical_order :
  forall l sub r p q,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    fst p = fst q ->
    region_above (classify l sub r p) (classify l sub r q) ->
    snd q < snd p.
Proof.
  intros l sub r p q Hne Hconn Hmono Hsparse Hx Habove.
  destruct (total_order_T (snd q) (snd p)) as [[Hlt | Heq] | Hgt].
  - exact Hlt.
  - exfalso. apply (region_above_not_reverse _ _ Habove).
    left. f_equal. destruct p as [xp yp], q as [xq yq].
    simpl in Hx, Heq |- *. f_equal; lra.
  - exfalso. apply (region_above_not_reverse _ _ Habove).
    eapply classified_same_x_monotone.
    + exact (classify_spec l sub r Hne Hconn Hmono Hsparse).
    + exact Hx.
    + exact Hgt.
Qed.

Lemma connected_x_monotone_endpoints :
  forall sub,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    fst (init (hd_segment sub)) < fst (term (last_segment sub)).
Proof.
  intros sub Hne. destruct sub as [|a tail]; [contradiction|].
  clear Hne.
  revert a. induction tail as [|b tail IH]; intros a Hconn Hmono.
  - apply Hmono. now left.
  - assert (Hab : term a = init b).
    { apply (Hconn 0%nat a b); reflexivity. }
    assert (HconnTail : connected (b :: tail)).
    { intros i s1 s2 H1 H2.
      apply (Hconn (S i) s1 s2); simpl; assumption. }
    assert (HmonoTail : x_monotone_segs (b :: tail)).
    { intros t Ht. apply Hmono. now right. }
    pose proof (IH b HconnTail HmonoTail) as Htail.
    pose proof (Hmono a ltac:(now left)) as Ha.
    change (fst (init a) < fst (term (last_segment (b :: tail)))).
    change (fst (init b) < fst (term (last_segment (b :: tail)))) in Htail.
    unfold x_monotone_seg, init_x, term_x in Ha.
    rewrite Hab in Ha. lra.
Qed.

(* x 単調な連結列では、全体長方形の左右端は列の始終点である。 *)
Lemma x_monotone_rect_x_bounds :
  forall sub,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    rx0 (rect_of sub) = fst (init (hd_segment sub))
    /\ rx1 (rect_of sub) = fst (term (last_segment sub)).
Proof.
  intros sub Hne Hconn Hmono.
  pose proof (connected_x_monotone_endpoints sub Hne Hconn Hmono) as Hends.
  unfold rect_of; simpl.
  rewrite Rmin_left by lra.
  rewrite Rmax_right by lra.
  split; reflexivity.
Qed.

(* セグメントの端点 x 区間内の各 x 座標は、セグメント上で実現される。 *)
Lemma segment_has_point_at_x :
  forall s x,
    rx0 (rect_of [s]) <= x <= rx1 (rect_of [s]) ->
    exists p, onSegment s p /\ fst p = x.
Proof.
  intros s x Hx.
  destruct (total_order_T (fst (init s)) (fst (term s)))
    as [[Hix | Heq] | Htx].
  - change (Rmin (fst (init s)) (fst (term s)) <= x <=
            Rmax (fst (init s)) (fst (term s))) in Hx.
    rewrite Rmin_left in Hx by lra.
    rewrite Rmax_right in Hx by lra.
    destruct (Rle_dec (snd (init s)) (snd (term s))) as [Hy | Hy].
    + destruct (exist_between_x_pos s
                  (fst (init s)) (fst (term s))
                  (snd (init s)) (snd (term s)) x
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  Hy (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
    + destruct (exist_between_x_neg s
                  (fst (init s)) (fst (term s))
                  (snd (init s)) (snd (term s)) x
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  ltac:(lra) (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
  - exfalso. apply (neq_init_term_x s).
    unfold init_x, term_x. exact Heq.
  - change (Rmin (fst (init s)) (fst (term s)) <= x <=
            Rmax (fst (init s)) (fst (term s))) in Hx.
    rewrite Rmin_right in Hx by lra.
    rewrite Rmax_left in Hx by lra.
    destruct (Rle_dec (snd (term s)) (snd (init s))) as [Hy | Hy].
    + destruct (exist_between_x_pos s
                  (fst (term s)) (fst (init s))
                  (snd (term s)) (snd (init s)) x
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  Hy (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
    + destruct (exist_between_x_neg s
                  (fst (term s)) (fst (init s))
                  (snd (term s)) (snd (init s)) x
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  ltac:(lra) (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
Qed.

(* 連結な x 単調 sub は、始終点間の各 x 座標を通る。 *)
Lemma x_monotone_sub_has_point :
  forall sub x,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    rx0 (rect_of sub) <= x <= rx1 (rect_of sub) ->
    exists q, onSegmentlist sub q /\ fst q = x.
Proof.
  intros sub x Hne. destruct sub as [|a tail]; [contradiction|].
  clear Hne. revert a x.
  induction tail as [|b tail IH]; intros a x Hconn Hmono Hx.
  - destruct (segment_has_point_at_x a x Hx) as [q [Hon Hqx]].
    exists q. split; [exists a; split; [now left | exact Hon] | exact Hqx].
  - assert (Hab : term a = init b).
    { apply (Hconn 0%nat a b); reflexivity. }
    assert (HconnTail : connected (b :: tail)).
    { intros i s1 s2 H1 H2.
      apply (Hconn (S i) s1 s2); simpl; assumption. }
    assert (HmonoTail : x_monotone_segs (b :: tail)).
    { intros s Hs. apply Hmono. now right. }
    pose proof (x_monotone_rect_x_bounds
                  (a :: b :: tail) ltac:(discriminate) Hconn Hmono)
      as [Hleft Hright].
    change (rx0 (rect_of (a :: b :: tail)) = fst (init a)) in Hleft.
    assert (Hlast :
      last_segment (a :: b :: tail) = last_segment (b :: tail)).
    { change (last_segment ([a] ++ b :: tail) = last_segment (b :: tail)).
      apply last_app_nonnil. discriminate. }
    rewrite Hleft, Hright in Hx.
    destruct (Rle_dec x (fst (term a))) as [Hxa | Hax].
    + assert (Hsingle :
          rx0 (rect_of [a]) <= x <= rx1 (rect_of [a])).
      { pose proof (Hmono a ltac:(now left)) as Ha.
        unfold x_monotone_seg, init_x, term_x in Ha.
        change (Rmin (fst (init a)) (fst (term a)) <= x <=
                Rmax (fst (init a)) (fst (term a))).
        rewrite Rmin_left by lra. rewrite Rmax_right by lra.
        lra. }
      destruct (segment_has_point_at_x a x Hsingle) as [q [Hon Hqx]].
      exists q. split.
      * exists a. split; [now left | exact Hon].
      * exact Hqx.
    + assert (Htailx :
          rx0 (rect_of (b :: tail)) <= x <=
          rx1 (rect_of (b :: tail))).
      { pose proof (x_monotone_rect_x_bounds
                      (b :: tail) ltac:(discriminate)
                      HconnTail HmonoTail) as [HtailLeft HtailRight].
        change (rx0 (rect_of (b :: tail)) = fst (init b)) in HtailLeft.
        rewrite HtailLeft, HtailRight.
        rewrite Hlast in Hx.
        rewrite Hab in Hax. lra. }
      destruct (IH b x HconnTail HmonoTail Htailx)
        as [q [[s [Hs Hon]] Hqx]].
      exists q. split.
      * exists s. split; [now right | exact Hon].
      * exact Hqx.
Qed.

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
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    0 < h ->
    operate_point l sub r h p = operate_point l sub r h q ->
    p = q.
Proof.
  intros l sub r h [xp yp] [xq yq]
    Hne Hconn Hmono Hsparse Hh Heq.
  destruct (classify l sub r (xp, yp)) eqn:Hrp;
  destruct (classify l sub r (xq, yq)) eqn:Hrq;
  unfold operate_point, shift in Heq; rewrite Hrp, Hrq in Heq;
  pose proof (f_equal fst Heq) as Hx;
  pose proof (f_equal snd Heq) as Hy; simpl in Hx, Hy.
  - f_equal; lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xq, yq) (xp, yp) Hne Hconn Hmono Hsparse
                  ltac:(symmetry; exact Hx)
                  ltac:(rewrite Hrq, Hrp; constructor)) as Horder.
    simpl in Horder. lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xp, yp) (xq, yq) Hne Hconn Hmono Hsparse
                  ltac:(exact Hx)
                  ltac:(rewrite Hrp, Hrq; constructor)) as Horder.
    simpl in Horder. lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xp, yp) (xq, yq) Hne Hconn Hmono Hsparse
                  ltac:(exact Hx)
                  ltac:(rewrite Hrp, Hrq; constructor)) as Horder.
    simpl in Horder. lra.
  - f_equal; lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xp, yp) (xq, yq) Hne Hconn Hmono Hsparse
                  ltac:(exact Hx)
                  ltac:(rewrite Hrp, Hrq; constructor)) as Horder.
    simpl in Horder. lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xq, yq) (xp, yp) Hne Hconn Hmono Hsparse
                  ltac:(symmetry; exact Hx)
                  ltac:(rewrite Hrq, Hrp; constructor)) as Horder.
    simpl in Horder. lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xq, yq) (xp, yp) Hne Hconn Hmono Hsparse
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
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    endpoint_of sub p ->
    classify l sub r p = RegFix.
Proof.
  intros l sub r p Hne Hconn Hmono Hsparse Hend.
  exact (classified_sub_fixed
           l sub r
           (classify_spec l sub r Hne Hconn Hmono Hsparse)
           p (endpoint_of_onSegmentlist sub p Hend)).
Qed.

Lemma operate_sub_endpoint :
  forall l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    endpoint_of sub p ->
    operate_point l sub r h p = p.
Proof.
  intros l sub r h p Hne Hconn Hmono Hsparse Hend.
  apply operate_point_RegFix.
  now apply classify_sub_endpoint.
Qed.

