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
From Stdlib Require Import Relations.Relation_Operators.

Require Export Sparsity.

(* ================================================================= *)
(*  1.  端点だけに意味を持つ分類                                     *)
(* ================================================================= *)

Inductive Region : Type := RegFix | RegUp | RegDown.

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

(* x 方向の閉区間が交わる二つの端点長方形。 *)
Definition segment_x_ranges_overlap (s t : Segment) : Prop :=
  rx0 (rect_of [s]) <= rx1 (rect_of [t])
  /\ rx0 (rect_of [t]) <= rx1 (rect_of [s]).

(* 以下の三補題は分類には依存しないが、延長線と sub の比較で使う。 *)
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
    { intros seg Hseg. apply Hmono. now right. }
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
        rewrite Rmin_left by lra. rewrite Rmax_right by lra. lra. }
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
        rewrite Hlast in Hx. rewrite Hab in Hax. lra. }
      destruct (IH b x HconnTail HmonoTail Htailx)
        as [q [[seg [Hseg Hon]] Hqx]].
      exists q. split.
      * exists seg. split; [now right | exact Hon].
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

Record ClassificationContext
    (l sub r : list Segment) : Prop := {
  context_sub_nonempty : sub <> [];
  context_sub_connected : connected sub;
  context_sub_x_monotone : x_monotone_segs sub;
  context_sparse : sparse_embedding (l ++ sub ++ r);
  context_whole_connected : connected (l ++ sub ++ r);
  context_whole_embedded :
    exists ds, embed_listDir ds (l ++ sub ++ r)
}.

(* 仕様の結論で分類する点は sub 上の点または端点だけである。
   [p], [q], [e] は上下関係を示す幾何学的な証人であり分類しない。 *)
Record ClassificationSpec
    (l sub r : list Segment) {classifier : EndpointClassifier} : Prop := {
  (* sub は全点を固定する。特に左右との接続端点も動かない。 *)
  classified_sub_fixed :
    forall p, onSegmentlist sub p -> classifier p = RegFix;

  (* 一セグメントの上下の端点順序を移動後も保存する。 *)
  classified_segment_endpoints_monotone :
    forall seg,
      In seg (l ++ sub ++ r) ->
      (snd (init seg) < snd (term seg) ->
        region_at_or_above (classifier (term seg)) (classifier (init seg)))
      /\
      (snd (term seg) < snd (init seg) ->
        region_at_or_above (classifier (init seg)) (classifier (term seg)));

  (* x 範囲が重なる非隣接セグメントの端点順序を保存する。 *)
  classified_nonadjacent_endpoint_order :
    forall i j s t ps pt,
      nth_error (l ++ sub ++ r) i = Some s ->
      nth_error (l ++ sub ++ r) j = Some t ->
      (S i < j \/ S j < i)%nat ->
      segment_x_ranges_overlap s t ->
      endpoint_of_seg s ps ->
      endpoint_of_seg t pt ->
      snd ps <= snd pt ->
      region_at_or_above (classifier pt) (classifier ps);

  (* sub の x 範囲でその上側・下側を通る非隣接セグメントは、
     両端を同じ外側へ動かす。 *)
  classified_segment_at_sub_x :
    forall seg p,
      In seg (nonadjacent_sides l r) ->
      onSegment seg p ->
      in_sub_x_range sub p ->
      (above_sub_at_x sub p ->
         classifier (init seg) = RegUp
         /\ classifier (term seg) = RegUp)
      /\
      (below_sub_at_x sub p ->
         classifier (init seg) = RegDown
         /\ classifier (term seg) = RegDown);

  (* strict 先頭延長線が sub の x 範囲へ入るなら、その基点を動かす。 *)
  classified_head_extension_at_sub_x :
    forall p,
      onHead_extend_strict (l ++ sub ++ r) p ->
      rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub) ->
      classifier (init (hd_segment (l ++ sub ++ r))) = RegUp
      \/ classifier (init (hd_segment (l ++ sub ++ r))) = RegDown;

  (* strict 末尾延長線についても、その基点を固定しない。 *)
  classified_last_extension_at_sub_x :
    forall p,
      onLast_extend_strict (l ++ sub ++ r) p ->
      rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub) ->
      classifier (term (last_segment (l ++ sub ++ r))) = RegUp
      \/ classifier (term (last_segment (l ++ sub ++ r))) = RegDown;

  (* 同じ x にある先頭・末尾延長線の上下順序を基点分類へ移す。 *)
  classified_head_last_extension_order :
    forall ph pl,
      onHead_extend (l ++ sub ++ r) ph ->
      onLast_extend (l ++ sub ++ r) pl ->
      fst ph = fst pl ->
      (snd ph < snd pl ->
         region_at_or_above
           (classifier (term (last_segment (l ++ sub ++ r))))
           (classifier (init (hd_segment (l ++ sub ++ r)))))
      /\
      (snd pl < snd ph ->
         region_at_or_above
           (classifier (init (hd_segment (l ++ sub ++ r))))
           (classifier (term (last_segment (l ++ sub ++ r)))));

  (* 先頭延長線と一セグメントの上下順序を三つの端点分類へ移す。 *)
  classified_head_segment_crossing_order :
    forall seg e q,
      In seg (l ++ sub ++ r) ->
      onSegment seg e ->
      onHead_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      (snd q < snd e ->
         region_at_or_above
           (classifier (init seg))
           (classifier (init (hd_segment (l ++ sub ++ r))))
         /\ region_at_or_above
           (classifier (term seg))
           (classifier (init (hd_segment (l ++ sub ++ r)))))
      /\
      (snd e < snd q ->
         region_at_or_above
           (classifier (init (hd_segment (l ++ sub ++ r))))
           (classifier (init seg))
         /\ region_at_or_above
           (classifier (init (hd_segment (l ++ sub ++ r))))
           (classifier (term seg)));

  (* 末尾延長線についても同じ端点順序を要求する。 *)
  classified_last_segment_crossing_order :
    forall seg e q,
      In seg (l ++ sub ++ r) ->
      onSegment seg e ->
      onLast_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      (snd q < snd e ->
         region_at_or_above
           (classifier (init seg))
           (classifier (term (last_segment (l ++ sub ++ r))))
         /\ region_at_or_above
           (classifier (term seg))
           (classifier (term (last_segment (l ++ sub ++ r)))))
      /\
      (snd e < snd q ->
         region_at_or_above
           (classifier (term (last_segment (l ++ sub ++ r))))
           (classifier (init seg))
         /\ region_at_or_above
           (classifier (term (last_segment (l ++ sub ++ r))))
           (classifier (term seg)));

  (* 分類どおりに任意の非負高さだけ動かしても、先頭の始点傾きを保てる。 *)
  classified_head_init_slope_reconnectable :
    forall h,
      0 <= h ->
      l <> [] ->
      classified_init_slope_reconnectable
        classifier h (hd_segment l);

  (* 末尾については終点傾きを保って再接続できる。 *)
  classified_last_term_slope_reconnectable :
    forall h,
      0 <= h ->
      r <> [] ->
      classified_term_slope_reconnectable
        classifier h (last_segment r)
}.

(* ----------------------------------------------------------------- *)
(*  端点制約                                                         *)
(* ----------------------------------------------------------------- *)

(* [endpoint_order_step p q] は、q の領域を p の領域以上にする
   直接の幾何学的制約を表す。 *)
Inductive endpoint_order_step
    (l sub r : list Segment) : Point -> Point -> Prop :=
  | order_on_segment : forall seg p q,
      In seg (l ++ sub ++ r) ->
      endpoint_of_seg seg p ->
      endpoint_of_seg seg q ->
      snd p <= snd q ->
      endpoint_order_step l sub r p q
  (* この二形の先頭では、始点傾きを任意の高さで保つため両端を
     同じ領域にする。通常の端点順序とは逆向きの制約だけを加える。 *)
  | order_head_north_cx_reverse : forall hor,
      l <> [] ->
      embed (n, hor, cx) (hd_segment l) ->
      endpoint_order_step l sub r
        (term (hd_segment l)) (init (hd_segment l))
  | order_head_south_cc_reverse : forall hor,
      l <> [] ->
      embed (s, hor, cc) (hd_segment l) ->
      endpoint_order_step l sub r
        (init (hd_segment l)) (term (hd_segment l))
  (* 末尾側では、終点傾きを保つために必要な二形で逆向き制約を加える。 *)
  | order_last_north_cc_reverse : forall hor,
      r <> [] ->
      embed (n, hor, cc) (last_segment r) ->
      endpoint_order_step l sub r
        (term (last_segment r)) (init (last_segment r))
  | order_last_south_cx_reverse : forall hor,
      r <> [] ->
      embed (s, hor, cx) (last_segment r) ->
      endpoint_order_step l sub r
        (init (last_segment r)) (term (last_segment r))
  | order_nonadjacent : forall i j s t ps pt,
      nth_error (l ++ sub ++ r) i = Some s ->
      nth_error (l ++ sub ++ r) j = Some t ->
      (S i < j \/ S j < i)%nat ->
      segment_x_ranges_overlap s t ->
      endpoint_of_seg s ps ->
      endpoint_of_seg t pt ->
      snd ps <= snd pt ->
      endpoint_order_step l sub r ps pt
  | order_head_last : forall ph pl,
      onHead_extend (l ++ sub ++ r) ph ->
      onLast_extend (l ++ sub ++ r) pl ->
      fst ph = fst pl ->
      snd ph <= snd pl ->
      endpoint_order_step l sub r
        (init (hd_segment (l ++ sub ++ r)))
        (term (last_segment (l ++ sub ++ r)))
  | order_last_head : forall ph pl,
      onHead_extend (l ++ sub ++ r) ph ->
      onLast_extend (l ++ sub ++ r) pl ->
      fst ph = fst pl ->
      snd pl <= snd ph ->
      endpoint_order_step l sub r
        (term (last_segment (l ++ sub ++ r)))
        (init (hd_segment (l ++ sub ++ r)))
  | order_head_below_segment : forall seg e q p,
      In seg (l ++ sub ++ r) ->
      onSegment seg e ->
      onHead_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      snd q <= snd e ->
      endpoint_of_seg seg p ->
      endpoint_order_step l sub r
        (init (hd_segment (l ++ sub ++ r))) p
  | order_segment_below_head : forall seg e q p,
      In seg (l ++ sub ++ r) ->
      onSegment seg e ->
      onHead_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      snd e <= snd q ->
      endpoint_of_seg seg p ->
      endpoint_order_step l sub r p
        (init (hd_segment (l ++ sub ++ r)))
  | order_last_below_segment : forall seg e q p,
      In seg (l ++ sub ++ r) ->
      onSegment seg e ->
      onLast_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      snd q <= snd e ->
      endpoint_of_seg seg p ->
      endpoint_order_step l sub r
        (term (last_segment (l ++ sub ++ r))) p
  | order_segment_below_last : forall seg e q p,
      In seg (l ++ sub ++ r) ->
      onSegment seg e ->
      onLast_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      snd e <= snd q ->
      endpoint_of_seg seg p ->
      endpoint_order_step l sub r p
        (term (last_segment (l ++ sub ++ r))).

Definition endpoint_order (l sub r : list Segment) : Point -> Point -> Prop :=
  clos_refl_trans Point (endpoint_order_step l sub r).

(* sub より上を通るセグメントの両端と、sub より上を通る strict
   延長線の基点が Up の種になる。 *)
Definition endpoint_up_seed
    (l sub r : list Segment) (p : Point) : Prop :=
  endpoint_of (l ++ sub ++ r) p
  /\
  ((exists seg q,
      In seg (nonadjacent_sides l r)
      /\ endpoint_of_seg seg p
      /\ onSegment seg q
      /\ in_sub_x_range sub q
      /\ above_sub_at_x sub q)
   \/ (p = init (hd_segment (l ++ sub ++ r))
       /\ exists q z,
            onHead_extend_strict (l ++ sub ++ r) q
            /\ onSegmentlist sub z
            /\ fst q = fst z
            /\ snd z < snd q)
   \/ (p = term (last_segment (l ++ sub ++ r))
       /\ exists q z,
            onLast_extend_strict (l ++ sub ++ r) q
            /\ onSegmentlist sub z
            /\ fst q = fst z
            /\ snd z < snd q)).

Definition endpoint_down_seed
    (l sub r : list Segment) (p : Point) : Prop :=
  endpoint_of (l ++ sub ++ r) p
  /\
  ((exists seg q,
      In seg (nonadjacent_sides l r)
      /\ endpoint_of_seg seg p
      /\ onSegment seg q
      /\ in_sub_x_range sub q
      /\ below_sub_at_x sub q)
   \/ (p = init (hd_segment (l ++ sub ++ r))
       /\ exists q z,
            onHead_extend_strict (l ++ sub ++ r) q
            /\ onSegmentlist sub z
            /\ fst q = fst z
            /\ snd q < snd z)
   \/ (p = term (last_segment (l ++ sub ++ r))
       /\ exists q z,
            onLast_extend_strict (l ++ sub ++ r) q
            /\ onSegmentlist sub z
            /\ fst q = fst z
            /\ snd q < snd z)).

(* Up は順序の上向き、Down は順序の下向きへ閉じる。 *)
Definition endpoint_forced_up
    (l sub r : list Segment) (p : Point) : Prop :=
  exists seed,
    endpoint_up_seed l sub r seed
    /\ endpoint_order l sub r seed p.

Definition endpoint_forced_down
    (l sub r : list Segment) (p : Point) : Prop :=
  exists seed,
    endpoint_down_seed l sub r seed
    /\ endpoint_order l sub r p seed.

Definition constraint_classifier
    (l sub r : list Segment) (p : Point) : Region :=
  if excluded_middle_informative (onSegmentlist sub p) then RegFix
  else if excluded_middle_informative (endpoint_of (l ++ sub ++ r) p) then
    if excluded_middle_informative (endpoint_forced_up l sub r p) then RegUp
    else if excluded_middle_informative (endpoint_forced_down l sub r p)
         then RegDown else RegFix
  else RegFix.

Definition classify := constraint_classifier.

Lemma endpoint_forced_up_order : forall l sub r p q,
  endpoint_order l sub r p q ->
  endpoint_forced_up l sub r p ->
  endpoint_forced_up l sub r q.
Proof.
  intros l sub r p q Hpq [seed [Hseed Hseedp]].
  exists seed. split; [exact Hseed |].
  eapply rt_trans; eauto.
Qed.

Lemma endpoint_forced_down_order : forall l sub r p q,
  endpoint_order l sub r p q ->
  endpoint_forced_down l sub r q ->
  endpoint_forced_down l sub r p.
Proof.
  intros l sub r p q Hpq [seed [Hseed Hqseed]].
  exists seed. split; [exact Hseed |].
  eapply rt_trans; eauto.
Qed.

Lemma whole_nonempty : forall (l sub r : list Segment),
  sub <> [] -> l ++ sub ++ r <> [].
Proof.
  intros l sub r Hsub Hnil.
  apply app_eq_nil in Hnil as [_ Hnil].
  apply app_eq_nil in Hnil as [Hbad _]. contradiction.
Qed.

Lemma head_endpoint_of : forall (ls : list Segment),
  ls <> [] -> endpoint_of ls (init (hd_segment ls)).
Proof.
  intros [|a ls] Hne; [contradiction |].
  exists a. split; [now left | now left].
Qed.

Lemma last_endpoint_of : forall (ls : list Segment),
  ls <> [] -> endpoint_of ls (term (last_segment ls)).
Proof.
  intros ls Hne. exists (last_segment ls). split.
  - now apply last_In.
  - now right.
Qed.

Lemma nonadjacent_sides_in_whole : forall l sub r seg,
  In seg (nonadjacent_sides l r) -> In seg (l ++ sub ++ r).
Proof.
  intros l sub r seg Hseg. unfold nonadjacent_sides in Hseg.
  rewrite in_app_iff in Hseg. rewrite !in_app_iff.
  destruct Hseg as [Hl | Hr].
  - left. now apply in_removelast_in.
  - right. right. destruct r as [|a r]; [contradiction |].
    simpl in Hr |- *. now right.
Qed.

(* Up の種から Down の種または sub へは進めず、sub から
   Down の種へも進めない。これが端点順序に残る中心的な幾何補題である。 *)
Axiom endpoint_order_separates_sources :
  forall l sub r,
    ClassificationContext l sub r ->
    forall upper lower,
      ((endpoint_up_seed l sub r upper
        /\ (endpoint_down_seed l sub r lower
            \/ onSegmentlist sub lower))
       \/ (onSegmentlist sub upper
           /\ endpoint_down_seed l sub r lower)) ->
      ~ endpoint_order l sub r upper lower.

(* 上の分離補題により、一点が Up/Down の双方から強制されることはない。 *)
Lemma endpoint_forcing_disjoint :
  forall l sub r,
    ClassificationContext l sub r ->
    forall p,
      ~ (endpoint_forced_up l sub r p
         /\ endpoint_forced_down l sub r p).
Proof.
  intros l sub r Hctx p [[up [Hup Hupp]] [down [Hdown Hpdown]]].
  apply (endpoint_order_separates_sources
           l sub r Hctx up down (or_introl (conj Hup (or_introl Hdown)))).
  eapply rt_trans; eauto.
Qed.

(* sub 上の点は、Up/Down のどちらの到達閉包にも入らない。 *)
Lemma sub_points_not_forced :
  forall l sub r,
    ClassificationContext l sub r ->
    forall p,
      onSegmentlist sub p ->
      ~ endpoint_forced_up l sub r p
      /\ ~ endpoint_forced_down l sub r p.
Proof.
  intros l sub r Hctx p Hsub. split.
  - intros [up [Hup Horder]].
    exact (endpoint_order_separates_sources
             l sub r Hctx up p
             (or_introl (conj Hup (or_intror Hsub))) Horder).
  - intros [down [Hdown Horder]].
    exact (endpoint_order_separates_sources
             l sub r Hctx p down
             (or_intror (conj Hsub Hdown)) Horder).
Qed.

(* 元のセグメント自身が、元の両端点・向き・両傾きによる再接続を与える。 *)
Lemma segment_reconnect_slope : forall seg,
  reconnect_slope
    (init seg) (term seg) (orn_seg seg) (slope_init seg) (slope_term seg).
Proof.
  intro seg.
  apply (proj2 (reconnect_slope_spec _ _ _ _ _)).
  exists seg. repeat split; reflexivity.
Qed.

(* 上下に並ぶ二領域では、上側の移動を差し引けば下側は下降し、
   下側の移動を差し引けば上側は上昇する。 *)
Lemma relative_shift_order : forall h lower upper p,
  0 <= h ->
  region_at_or_above upper lower ->
  snd (translate_pt (opposite_translation (region_translation h upper))
         (shift h lower p)) <= snd p
  /\ snd p <=
     snd (translate_pt (opposite_translation (region_translation h lower))
            (shift h upper p)).
Proof.
  intros h lower upper [x y] Hh Horder.
  destruct lower, upper; unfold shift, region_translation, translate_pt,
    opposite_translation in *; simpl in *;
    destruct Horder as [Horder | Horder];
    try discriminate; try inversion Horder; split; lra.
Qed.

(* 両端が同じ領域なら、元のセグメントをそのまま平行移動できる。 *)
Lemma classified_init_slope_same_region :
  forall classifier h seg,
    classifier (init seg) = classifier (term seg) ->
    classified_init_slope_reconnectable classifier h seg.
Proof.
  intros classifier h seg Hsame.
  unfold classified_init_slope_reconnectable.
  rewrite <- Hsame, !shift_as_translation.
  apply reconnect_init_slope_translate.
  exists (slope_term seg). apply segment_reconnect_slope.
Qed.

(* 終点の移動を共通平行移動として取り除き、始点だけを下げる公理へ帰着する。 *)
Lemma classified_init_slope_relative_lower :
  forall classifier h seg,
    0 <= h ->
    region_at_or_above
      (classifier (term seg)) (classifier (init seg)) ->
    (forall p,
      fst p = fst (init seg) ->
      snd p <= snd (init seg) ->
      reconnect_init_slope
        p (term seg) (orn_seg seg) (slope_init seg)) ->
    classified_init_slope_reconnectable classifier h seg.
Proof.
  intros classifier h seg Hh Horder Hlower.
  set (gi := classifier (init seg)).
  set (gt := classifier (term seg)).
  set (v := region_translation h gt).
  set (p0 := translate_pt (opposite_translation v) (shift h gi (init seg))).
  assert (Hx : fst p0 = fst (init seg)).
  { unfold p0, v, gi, gt, opposite_translation, translate_pt,
      region_translation, shift.
    destruct (classifier (init seg));
      destruct (classifier (term seg)); destruct (init seg); simpl; ring. }
  assert (Hy : snd p0 <= snd (init seg)).
  { unfold p0, v, gi, gt.
    exact (proj1 (relative_shift_order h gi gt (init seg) Hh Horder)). }
  pose proof (reconnect_init_slope_translate
                v p0 (term seg) (orn_seg seg) (slope_init seg)
                (Hlower p0 Hx Hy)) as Htranslated.
  assert (Hp : translate_pt v p0 = shift h gi (init seg)).
  { unfold p0. apply translate_pt_opposite_left. }
  assert (Hq : translate_pt v (term seg) = shift h gt (term seg)).
  { unfold v. symmetry. apply shift_as_translation. }
  unfold classified_init_slope_reconnectable.
  fold gi gt. now rewrite <- Hp, <- Hq.
Qed.

(* 上向きの場合も、終点の移動を差し引いて始点だけの変形にする。 *)
Lemma classified_init_slope_relative_upper :
  forall classifier h seg,
    0 <= h ->
    region_at_or_above
      (classifier (init seg)) (classifier (term seg)) ->
    (forall p,
      fst p = fst (init seg) ->
      snd (init seg) <= snd p ->
      reconnect_init_slope
        p (term seg) (orn_seg seg) (slope_init seg)) ->
    classified_init_slope_reconnectable classifier h seg.
Proof.
  intros classifier h seg Hh Horder Hraise.
  set (gi := classifier (init seg)).
  set (gt := classifier (term seg)).
  set (v := region_translation h gt).
  set (p0 := translate_pt (opposite_translation v) (shift h gi (init seg))).
  assert (Hx : fst p0 = fst (init seg)).
  { unfold p0, v, gi, gt, opposite_translation, translate_pt,
      region_translation, shift.
    destruct (classifier (init seg));
      destruct (classifier (term seg)); destruct (init seg); simpl; ring. }
  assert (Hy : snd (init seg) <= snd p0).
  { unfold p0, v, gi, gt.
    exact (proj2 (relative_shift_order h gt gi (init seg) Hh Horder)). }
  pose proof (reconnect_init_slope_translate
                v p0 (term seg) (orn_seg seg) (slope_init seg)
                (Hraise p0 Hx Hy)) as Htranslated.
  assert (Hp : translate_pt v p0 = shift h gi (init seg)).
  { unfold p0. apply translate_pt_opposite_left. }
  assert (Hq : translate_pt v (term seg) = shift h gt (term seg)).
  { unfold v. symmetry. apply shift_as_translation. }
  unfold classified_init_slope_reconnectable.
  fold gi gt. now rewrite <- Hp, <- Hq.
Qed.

Lemma classified_term_slope_same_region :
  forall classifier h seg,
    classifier (init seg) = classifier (term seg) ->
    classified_term_slope_reconnectable classifier h seg.
Proof.
  intros classifier h seg Hsame.
  unfold classified_term_slope_reconnectable.
  rewrite <- Hsame, !shift_as_translation.
  apply reconnect_term_slope_translate.
  exists (slope_init seg). apply segment_reconnect_slope.
Qed.

Lemma classified_term_slope_relative_upper :
  forall classifier h seg,
    0 <= h ->
    region_at_or_above
      (classifier (term seg)) (classifier (init seg)) ->
    (forall p,
      fst p = fst (term seg) ->
      snd (term seg) <= snd p ->
      reconnect_term_slope
        (init seg) p (orn_seg seg) (slope_term seg)) ->
    classified_term_slope_reconnectable classifier h seg.
Proof.
  intros classifier h seg Hh Horder Hraise.
  set (gi := classifier (init seg)).
  set (gt := classifier (term seg)).
  set (v := region_translation h gi).
  set (q0 := translate_pt (opposite_translation v) (shift h gt (term seg))).
  assert (Hx : fst q0 = fst (term seg)).
  { unfold q0, v, gi, gt, opposite_translation, translate_pt,
      region_translation, shift.
    destruct (classifier (init seg));
      destruct (classifier (term seg)); destruct (term seg); simpl; ring. }
  assert (Hy : snd (term seg) <= snd q0).
  { unfold q0, v, gi, gt.
    exact (proj2 (relative_shift_order h gi gt (term seg) Hh Horder)). }
  pose proof (reconnect_term_slope_translate
                v (init seg) q0 (orn_seg seg) (slope_term seg)
                (Hraise q0 Hx Hy)) as Htranslated.
  assert (Hp : translate_pt v (init seg) = shift h gi (init seg)).
  { unfold v. symmetry. apply shift_as_translation. }
  assert (Hq : translate_pt v q0 = shift h gt (term seg)).
  { unfold q0. apply translate_pt_opposite_left. }
  unfold classified_term_slope_reconnectable.
  fold gi gt. now rewrite <- Hp, <- Hq.
Qed.

Lemma classified_term_slope_relative_lower :
  forall classifier h seg,
    0 <= h ->
    region_at_or_above
      (classifier (init seg)) (classifier (term seg)) ->
    (forall p,
      fst p = fst (term seg) ->
      snd p <= snd (term seg) ->
      reconnect_term_slope
        (init seg) p (orn_seg seg) (slope_term seg)) ->
    classified_term_slope_reconnectable classifier h seg.
Proof.
  intros classifier h seg Hh Horder Hlower.
  set (gi := classifier (init seg)).
  set (gt := classifier (term seg)).
  set (v := region_translation h gi).
  set (q0 := translate_pt (opposite_translation v) (shift h gt (term seg))).
  assert (Hx : fst q0 = fst (term seg)).
  { unfold q0, v, gi, gt, opposite_translation, translate_pt,
      region_translation, shift.
    destruct (classifier (init seg));
      destruct (classifier (term seg)); destruct (term seg); simpl; ring. }
  assert (Hy : snd q0 <= snd (term seg)).
  { unfold q0, v, gi, gt.
    exact (proj1 (relative_shift_order h gt gi (term seg) Hh Horder)). }
  pose proof (reconnect_term_slope_translate
                v (init seg) q0 (orn_seg seg) (slope_term seg)
                (Hlower q0 Hx Hy)) as Htranslated.
  assert (Hp : translate_pt v (init seg) = shift h gi (init seg)).
  { unfold v. symmetry. apply shift_as_translation. }
  assert (Hq : translate_pt v q0 = shift h gt (term seg)).
  { unfold q0. apply translate_pt_opposite_left. }
  unfold classified_term_slope_reconnectable.
  fold gi gt. now rewrite <- Hp, <- Hq.
Qed.

Lemma endpoint_seed_forced_up : forall l sub r p,
  endpoint_up_seed l sub r p -> endpoint_forced_up l sub r p.
Proof.
  intros l sub r p Hseed. exists p. split; [exact Hseed | apply rt_refl].
Qed.

Lemma endpoint_seed_forced_down : forall l sub r p,
  endpoint_down_seed l sub r p -> endpoint_forced_down l sub r p.
Proof.
  intros l sub r p Hseed. exists p. split; [exact Hseed | apply rt_refl].
Qed.

Lemma classify_forced_up : forall l sub r p
  (Hctx : ClassificationContext l sub r),
  endpoint_of (l ++ sub ++ r) p ->
  endpoint_forced_up l sub r p ->
  classify l sub r p = RegUp.
Proof.
  intros l sub r p Hctx Hend Hup.
  unfold classify, constraint_classifier.
  destruct (excluded_middle_informative (onSegmentlist sub p)) as [Hsub | Hsub].
  - exfalso. exact (proj1 (sub_points_not_forced l sub r Hctx p Hsub) Hup).
  - destruct (excluded_middle_informative (endpoint_of (l ++ sub ++ r) p));
      [|contradiction].
    destruct (excluded_middle_informative (endpoint_forced_up l sub r p));
      [reflexivity | contradiction].
Qed.

Lemma classify_forced_down : forall l sub r p
  (Hctx : ClassificationContext l sub r),
  endpoint_of (l ++ sub ++ r) p ->
  endpoint_forced_down l sub r p ->
  classify l sub r p = RegDown.
Proof.
  intros l sub r p Hctx Hend Hdown.
  unfold classify, constraint_classifier.
  destruct (excluded_middle_informative (onSegmentlist sub p)) as [Hsub | Hsub].
  - exfalso. exact (proj2 (sub_points_not_forced l sub r Hctx p Hsub) Hdown).
  - destruct (excluded_middle_informative (endpoint_of (l ++ sub ++ r) p));
      [|contradiction].
    destruct (excluded_middle_informative (endpoint_forced_up l sub r p))
      as [Hup | Hup].
    + exfalso. exact (endpoint_forcing_disjoint l sub r Hctx p (conj Hup Hdown)).
    + destruct (excluded_middle_informative (endpoint_forced_down l sub r p));
        [reflexivity | contradiction].
Qed.

Lemma classify_up_forced : forall l sub r p,
  classify l sub r p = RegUp -> endpoint_forced_up l sub r p.
Proof.
  intros l sub r p Hclass.
  unfold classify, constraint_classifier in Hclass.
  repeat destruct excluded_middle_informative; try discriminate; assumption.
Qed.

Lemma classify_down_forced : forall l sub r p,
  classify l sub r p = RegDown -> endpoint_forced_down l sub r p.
Proof.
  intros l sub r p Hclass.
  unfold classify, constraint_classifier in Hclass.
  repeat destruct excluded_middle_informative; try discriminate; assumption.
Qed.

Lemma endpoint_order_classified : forall l sub r p q,
  ClassificationContext l sub r ->
  endpoint_of (l ++ sub ++ r) p ->
  endpoint_of (l ++ sub ++ r) q ->
  endpoint_order l sub r p q ->
  region_at_or_above (classify l sub r q) (classify l sub r p).
Proof.
  intros l sub r p q Hctx Hp Hq Horder.
  destruct (classify l sub r p) eqn:Hcp;
  destruct (classify l sub r q) eqn:Hcq.
  - now left.
  - now right; constructor.
  - exfalso.
    pose proof (classify_down_forced l sub r q Hcq) as Hdownq.
    pose proof (endpoint_forced_down_order l sub r p q Horder Hdownq) as Hdownp.
    pose proof (classify_forced_down l sub r p Hctx Hp Hdownp). congruence.
  - exfalso.
    pose proof (classify_up_forced l sub r p Hcp) as Hupp.
    pose proof (endpoint_forced_up_order l sub r p q Horder Hupp) as Hupq.
    pose proof (classify_forced_up l sub r q Hctx Hq Hupq). congruence.
  - now left.
  - exfalso.
    pose proof (classify_up_forced l sub r p Hcp) as Hupp.
    pose proof (endpoint_forced_up_order l sub r p q Horder Hupp) as Hupq.
    pose proof (classify_forced_up l sub r q Hctx Hq Hupq). congruence.
  - now right; constructor.
  - now right; constructor.
  - now left.
Qed.

(* 先頭を埋め込む PrimitiveSegment の四形ごとに、端点順序または
   追加した逆向き制約を使って始点傾きの保存へ帰着する。 *)
Lemma head_classification_preserves_init_slope :
  forall l sub r,
    ClassificationContext l sub r ->
    forall h,
      0 <= h ->
      l <> [] ->
      classified_init_slope_reconnectable
        (classify l sub r) h (hd_segment l).
Proof.
  intros [|seg tail] sub r Hctx h Hh Hl; [contradiction |].
  simpl in *.
  destruct (context_whole_embedded (seg :: tail) sub r Hctx)
    as [ds [sc [_ Hcurve]]].
  destruct (embed_scurve_nth_embed
              sc (seg :: tail ++ sub ++ r) Hcurve 0%nat seg eq_refl)
    as [[[vert hor] curv] [_ Hembed]].
  assert (HinitEnd : endpoint_of (seg :: tail ++ sub ++ r) (init seg)).
  { exists seg. split; [now left | now left]. }
  assert (HtermEnd : endpoint_of (seg :: tail ++ sub ++ r) (term seg)).
  { exists seg. split; [now left | now right]. }
  destruct vert, curv.
  - (* north, convex: the added reverse constraint forces equal regions. *)
    apply classified_init_slope_same_region.
    apply region_at_or_above_antisym.
    + eapply endpoint_order_classified; eauto.
      apply rt_step. eapply order_head_north_cx_reverse; eauto.
    + eapply endpoint_order_classified; eauto.
      apply rt_step. eapply order_on_segment with (seg := seg).
      * now left.
      * now left.
      * now right.
      * pose proof (n_end_relation seg hor cx Hembed). lra.
  - (* north, concave: the start moves weakly down relative to the end. *)
    apply classified_init_slope_relative_lower; [exact Hh | |].
    + eapply endpoint_order_classified; eauto.
      apply rt_step. eapply order_on_segment with (seg := seg).
      * now left.
      * now left.
      * now right.
      * pose proof (n_end_relation seg hor cc Hembed). lra.
    + destruct hor.
      * intros p Hx Hy. eapply northeast_cc_lower_init_slope; eauto.
      * intros p Hx Hy. eapply northwest_cc_lower_init_slope; eauto.
  - (* south, convex: the start moves weakly up relative to the end. *)
    apply classified_init_slope_relative_upper; [exact Hh | |].
    + eapply endpoint_order_classified; eauto.
      apply rt_step. eapply order_on_segment with (seg := seg).
      * now left.
      * now right.
      * now left.
      * pose proof (s_end_relation seg hor cx Hembed). lra.
    + destruct hor.
      * intros p Hx Hy. eapply southeast_cx_raise_init_slope; eauto.
      * intros p Hx Hy. eapply southwest_cx_raise_init_slope; eauto.
  - (* south, concave: the added reverse constraint forces equal regions. *)
    apply classified_init_slope_same_region.
    apply region_at_or_above_antisym.
    + eapply endpoint_order_classified; eauto.
      apply rt_step. eapply order_on_segment with (seg := seg).
      * now left.
      * now right.
      * now left.
      * pose proof (s_end_relation seg hor cc Hembed). lra.
    + eapply endpoint_order_classified; eauto.
      apply rt_step. eapply order_head_south_cc_reverse; eauto.
Qed.

(* 末尾では始点の移動を共通平行移動として除き、四形ごとに
   終点だけの上下移動または同領域の平行移動へ帰着する。 *)
Lemma last_classification_preserves_term_slope :
  forall l sub r,
    ClassificationContext l sub r ->
    forall h,
      0 <= h ->
      r <> [] ->
      classified_term_slope_reconnectable
        (classify l sub r) h (last_segment r).
Proof.
  intros l sub [|first rest] Hctx h Hh Hr; [contradiction |].
  set (seg := last_segment (first :: rest)).
  assert (HinR : In seg (first :: rest)).
  { unfold seg. apply last_In. discriminate. }
  assert (HinWhole : In seg (l ++ sub ++ first :: rest)).
  { rewrite !in_app_iff. tauto. }
  destruct (context_whole_embedded l sub (first :: rest) Hctx)
    as [ds [sc [_ Hcurve]]].
  destruct (In_nth_error (l ++ sub ++ first :: rest) seg HinWhole)
    as [i Hi].
  destruct (embed_scurve_nth_embed
              sc (l ++ sub ++ first :: rest) Hcurve i seg Hi)
    as [[[vert hor] curv] [_ Hembed]].
  assert (HinitEnd : endpoint_of (l ++ sub ++ first :: rest) (init seg)).
  { exists seg. split; [exact HinWhole | now left]. }
  assert (HtermEnd : endpoint_of (l ++ sub ++ first :: rest) (term seg)).
  { exists seg. split; [exact HinWhole | now right]. }
  destruct vert, curv.
  - (* north, convex: the end moves weakly up relative to the start. *)
    apply classified_term_slope_relative_upper; [exact Hh | |].
    + eapply endpoint_order_classified; eauto.
      apply rt_step. eapply order_on_segment with (seg := seg).
      * exact HinWhole.
      * now left.
      * now right.
      * pose proof (n_end_relation seg hor cx Hembed). lra.
    + destruct hor.
      * intros p Hx Hy. eapply northeast_cx_raise_term_slope; eauto.
      * intros p Hx Hy. eapply northwest_cx_raise_term_slope; eauto.
  - (* north, concave: the added reverse constraint forces equal regions. *)
    apply classified_term_slope_same_region.
    apply region_at_or_above_antisym.
    + eapply endpoint_order_classified; eauto.
      apply rt_step. eapply order_last_north_cc_reverse; eauto.
    + eapply endpoint_order_classified; eauto.
      apply rt_step. eapply order_on_segment with (seg := seg).
      * exact HinWhole.
      * now left.
      * now right.
      * pose proof (n_end_relation seg hor cc Hembed). lra.
  - (* south, convex: the added reverse constraint forces equal regions. *)
    apply classified_term_slope_same_region.
    apply region_at_or_above_antisym.
    + eapply endpoint_order_classified; eauto.
      apply rt_step. eapply order_on_segment with (seg := seg).
      * exact HinWhole.
      * now right.
      * now left.
      * pose proof (s_end_relation seg hor cx Hembed). lra.
    + eapply endpoint_order_classified; eauto.
      apply rt_step. eapply order_last_south_cx_reverse; eauto.
  - (* south, concave: the end moves weakly down relative to the start. *)
    apply classified_term_slope_relative_lower; [exact Hh | |].
    + eapply endpoint_order_classified; eauto.
      apply rt_step. eapply order_on_segment with (seg := seg).
      * exact HinWhole.
      * now right.
      * now left.
      * pose proof (s_end_relation seg hor cc Hembed). lra.
    + destruct hor.
      * intros p Hx Hy. eapply southeast_cc_lower_term_slope; eauto.
      * intros p Hx Hy. eapply southwest_cc_lower_term_slope; eauto.
Qed.

Lemma strict_extension_not_on_sub : forall l sub r p,
  sparse_embedding (l ++ sub ++ r) ->
  (onHead_extend_strict (l ++ sub ++ r) p
   \/ onLast_extend_strict (l ++ sub ++ r) p) ->
  onSegmentlist sub p -> False.
Proof.
  intros l sub r p Hsparse Hextend [seg [Hseg Hon]].
  apply in_split in Hseg.
  destruct Hseg as [sub_l [sub_r Hsub]]. subst sub.
  assert (Hwhole :
    l ++ (sub_l ++ seg :: sub_r) ++ r =
    (l ++ sub_l) ++ [seg] ++ (sub_r ++ r)).
  { repeat rewrite <- app_assoc. simpl. reflexivity. }
  destruct (Hsparse (l ++ sub_l) seg (sub_r ++ r) Hwhole)
    as [Havoid _].
  apply (Havoid p).
  - now rewrite <- Hwhole.
  - change (in_segment_rect_or_endpoints seg p).
    now apply segment_in_rect_or_endpoints.
Qed.

Lemma strict_extension_above_or_below_sub : forall l sub r p,
  ClassificationContext l sub r ->
  (onHead_extend_strict (l ++ sub ++ r) p
   \/ onLast_extend_strict (l ++ sub ++ r) p) ->
  in_sub_x_range sub p ->
  above_sub_at_x sub p \/ below_sub_at_x sub p.
Proof.
  intros l sub r [xp yp] Hctx Hextend Hx.
  destruct Hctx as [Hne Hconn Hmono Hsparse Hwhole Hembed].
  destruct (x_monotone_sub_has_point sub xp Hne Hconn Hmono Hx)
    as [[xz yz] [Hz Hxz]]. simpl in Hxz. subst xz.
  assert (Hneq : yp <> yz).
  { intros ->. eapply strict_extension_not_on_sub; eauto. }
  destruct (total_order_T yp yz) as [[Hbelow | Heq] | Habove].
  - right. exists (xp, yz). repeat split; assumption.
  - contradiction.
  - left. exists (xp, yz). repeat split; assumption.
Qed.

Lemma classify_spec :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    @ClassificationSpec l sub r (classify l sub r).
Proof.
  intros l sub r Hne Hconn Hmono Hsparse Hwhole Hembed.
  pose (Hctx := Build_ClassificationContext
                  l sub r Hne Hconn Hmono Hsparse Hwhole Hembed).
  assert (HwholeNe : l ++ sub ++ r <> []) by now apply whole_nonempty.
  constructor.
  - intros p Hp. unfold classify, constraint_classifier.
    destruct (excluded_middle_informative (onSegmentlist sub p));
      [reflexivity | contradiction].
  - intros seg Hseg. split; intros Hy.
    + eapply endpoint_order_classified; eauto.
      * exists seg. split; [exact Hseg | now left].
      * exists seg. split; [exact Hseg | now right].
      * apply rt_step. eapply order_on_segment with (seg := seg).
        -- exact Hseg.
        -- now left.
        -- now right.
        -- lra.
    + eapply endpoint_order_classified; eauto.
      * exists seg. split; [exact Hseg | now right].
      * exists seg. split; [exact Hseg | now left].
      * apply rt_step. eapply order_on_segment with (seg := seg).
        -- exact Hseg.
        -- now right.
        -- now left.
        -- lra.
  - intros i j s0 t ps pt Hs Ht Hij Hover Hps Hpt Hy.
    eapply endpoint_order_classified; eauto.
    + exists s0. split; [eapply nth_error_In; eauto | exact Hps].
    + exists t. split; [eapply nth_error_In; eauto | exact Hpt].
    + apply rt_step.
      exact (order_nonadjacent l sub r i j s0 t ps pt
               Hs Ht Hij Hover Hps Hpt Hy).
  - intros seg p Hseg Hon Hrange. split; intros Hside.
    + split; apply (classify_forced_up l sub r _ Hctx).
      * exists seg. split; [now apply nonadjacent_sides_in_whole | now left].
      * apply endpoint_seed_forced_up. split.
        -- exists seg. split; [now apply nonadjacent_sides_in_whole | now left].
        -- left. exists seg, p. split; [exact Hseg |].
           split; [now left |]. split; [exact Hon |].
           split; assumption.
      * exists seg. split; [now apply nonadjacent_sides_in_whole | now right].
      * apply endpoint_seed_forced_up. split.
        -- exists seg. split; [now apply nonadjacent_sides_in_whole | now right].
        -- left. exists seg, p. split; [exact Hseg |].
           split; [now right |]. split; [exact Hon |].
           split; assumption.
    + split; apply (classify_forced_down l sub r _ Hctx).
      * exists seg. split; [now apply nonadjacent_sides_in_whole | now left].
      * apply endpoint_seed_forced_down. split.
        -- exists seg. split; [now apply nonadjacent_sides_in_whole | now left].
        -- left. exists seg, p. split; [exact Hseg |].
           split; [now left |]. split; [exact Hon |].
           split; assumption.
      * exists seg. split; [now apply nonadjacent_sides_in_whole | now right].
      * apply endpoint_seed_forced_down. split.
        -- exists seg. split; [now apply nonadjacent_sides_in_whole | now right].
        -- left. exists seg, p. split; [exact Hseg |].
           split; [now right |]. split; [exact Hon |].
           split; assumption.
  - intros p Hext Hrange.
    destruct (strict_extension_above_or_below_sub l sub r p Hctx
                (or_introl Hext) Hrange) as [Habove | Hbelow].
    + left. apply (classify_forced_up l sub r _ Hctx).
      * now apply head_endpoint_of.
      * apply endpoint_seed_forced_up. split; [now apply head_endpoint_of |].
        right; left. split; [reflexivity |].
        destruct Habove as [z [Hz [Hx Hy]]].
        exists p, z. repeat split; assumption.
    + right. apply (classify_forced_down l sub r _ Hctx).
      * now apply head_endpoint_of.
      * apply endpoint_seed_forced_down. split; [now apply head_endpoint_of |].
        right; left. split; [reflexivity |].
        destruct Hbelow as [z [Hz [Hx Hy]]].
        exists p, z. repeat split; assumption.
  - intros p Hext Hrange.
    destruct (strict_extension_above_or_below_sub l sub r p Hctx
                (or_intror Hext) Hrange) as [Habove | Hbelow].
    + left. apply (classify_forced_up l sub r _ Hctx).
      * now apply last_endpoint_of.
      * apply endpoint_seed_forced_up. split; [now apply last_endpoint_of |].
        right; right. split; [reflexivity |].
        destruct Habove as [z [Hz [Hx Hy]]].
        exists p, z. repeat split; assumption.
    + right. apply (classify_forced_down l sub r _ Hctx).
      * now apply last_endpoint_of.
      * apply endpoint_seed_forced_down. split; [now apply last_endpoint_of |].
        right; right. split; [reflexivity |].
        destruct Hbelow as [z [Hz [Hx Hy]]].
        exists p, z. repeat split; assumption.
  - intros ph pl Hph Hpl Hx. split; intros Hy.
    + eapply endpoint_order_classified; eauto using head_endpoint_of, last_endpoint_of.
      apply rt_step. eapply order_head_last; eauto. lra.
    + eapply endpoint_order_classified; eauto using head_endpoint_of, last_endpoint_of.
      apply rt_step. eapply order_last_head; eauto. lra.
  - intros seg e q Hseg He Hq Hx. split; intros Hy; split.
    + eapply endpoint_order_classified; eauto using head_endpoint_of.
      * exists seg. split; [exact Hseg | now left].
      * apply rt_step. eapply order_head_below_segment; eauto; [lra | now left].
    + eapply endpoint_order_classified; eauto using head_endpoint_of.
      * exists seg. split; [exact Hseg | now right].
      * apply rt_step. eapply order_head_below_segment; eauto; [lra | now right].
    + eapply endpoint_order_classified; eauto using head_endpoint_of.
      * exists seg. split; [exact Hseg | now left].
      * apply rt_step. eapply order_segment_below_head; eauto; [lra | now left].
    + eapply endpoint_order_classified; eauto using head_endpoint_of.
      * exists seg. split; [exact Hseg | now right].
      * apply rt_step. eapply order_segment_below_head; eauto; [lra | now right].
  - intros seg e q Hseg He Hq Hx. split; intros Hy; split.
    + eapply endpoint_order_classified; eauto using last_endpoint_of.
      * exists seg. split; [exact Hseg | now left].
      * apply rt_step. eapply order_last_below_segment; eauto; [lra | now left].
    + eapply endpoint_order_classified; eauto using last_endpoint_of.
      * exists seg. split; [exact Hseg | now right].
      * apply rt_step. eapply order_last_below_segment; eauto; [lra | now right].
    + eapply endpoint_order_classified; eauto using last_endpoint_of.
      * exists seg. split; [exact Hseg | now left].
      * apply rt_step. eapply order_segment_below_last; eauto; [lra | now left].
    + eapply endpoint_order_classified; eauto using last_endpoint_of.
      * exists seg. split; [exact Hseg | now right].
      * apply rt_step. eapply order_segment_below_last; eauto; [lra | now right].
  - now apply head_classification_preserves_init_slope.
  - now apply last_classification_preserves_term_slope.
Qed.

(* ================================================================= *)
(*  2.  分類された端点の上下移動                                     *)
(* ================================================================= *)

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

Definition operate_point
    (l sub r : list Segment) (h : R) (p : Point) : Point :=
  shift h (classify l sub r p) p.

Lemma shift_fst :
  forall h g p, fst (shift h g p) = fst p.
Proof. intros. destruct g; reflexivity. Qed.

Lemma operate_point_fst :
  forall l sub r h p, fst (operate_point l sub r h p) = fst p.
Proof. intros. unfold operate_point. apply shift_fst. Qed.

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
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    endpoint_of sub p ->
    classify l sub r p = RegFix.
Proof.
  intros l sub r p Hne Hconn Hmono Hsparse Hwhole Hembed Hend.
  exact (classified_sub_fixed
           l sub r
           (classify_spec l sub r Hne Hconn Hmono Hsparse Hwhole Hembed)
           p (endpoint_of_onSegmentlist sub p Hend)).
Qed.

Lemma operate_sub_endpoint :
  forall l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    endpoint_of sub p ->
    operate_point l sub r h p = p.
Proof.
  intros l sub r h p Hne Hconn Hmono Hsparse Hwhole Hembed Hend.
  apply operate_point_RegFix.
  now apply classify_sub_endpoint.
Qed.
