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

(* [p] と同じ x にある sub 上の全ての点より、[p] が厳密に上にある。
   全称形にしておくと、sub 上への到達時には [q := p] で直ちに矛盾する。 *)
Definition strictly_above_sub_at_x
    (sub : list Segment) (p : Point) : Prop :=
  forall q,
    onSegmentlist sub q ->
    fst p = fst q ->
    snd q < snd p.

Lemma strictly_above_sub_at_x_not_on_sub : forall sub p,
  strictly_above_sub_at_x sub p ->
  ~ onSegmentlist sub p.
Proof.
  intros sub p Habove Hsub.
  specialize (Habove p Hsub eq_refl). lra.
Qed.

(* [p] が、sub と交わらず、共通 x の一点で sub より上にある連続
   trace に属することを表す。分類や端点順序には依存しない。 *)
Definition on_trace_above_sub (sub : list Segment) (p : Point) : Prop :=
  exists part seg p0 q0,
    trace_disjoint_from_segmentlist part seg sub
    /\ onSegmentTrace part seg p
    /\ onSegmentTrace part seg p0
    /\ onSegmentlist sub q0
    /\ fst p0 = fst q0
    /\ snd q0 < snd p0.

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

Lemma x_monotone_segment_point_bounds :
  forall s p,
    x_monotone_seg s ->
    onSegment s p ->
    fst (init s) <= fst p <= fst (term s).
Proof.
  intros s p Hmono Hp.
  destruct (segment_in_rectangle_or_endpoints s p Hp)
    as [-> | [-> | Hinside]].
  - unfold x_monotone_seg, init_x, term_x in Hmono. lra.
  - unfold x_monotone_seg, init_x, term_x in Hmono. lra.
  - unfold in_open_segment_rectangle, in_rect, rect_between in Hinside.
    cbn in Hinside.
    destruct Hinside as [Hx _].
    unfold x_monotone_seg, init_x, term_x in Hmono.
    rewrite Rmin_left in Hx by lra. rewrite Rmax_right in Hx by lra.
    lra.
Qed.

(* 連結な x 単調 sub 上の点は、その始点と終点が定める閉 x 範囲に入る。 *)
Lemma x_monotone_sub_point_in_x_range :
  forall sub p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    in_sub_x_range sub p.
Proof.
  intros sub p Hne. destruct sub as [|a tail]; [contradiction|].
  clear Hne. revert a p.
  induction tail as [|b tail IH]; intros a p Hconn Hmono
      [seg [Hseg Hon]].
  - simpl in Hseg. destruct Hseg as [Hseg | Hseg]; [subst seg | contradiction].
    pose proof (Hmono a ltac:(now left)) as Ha.
    pose proof (x_monotone_rect_x_bounds
                  [a] ltac:(discriminate) Hconn Hmono) as [Hleft Hright].
    pose proof (x_monotone_segment_point_bounds a p Ha Hon) as Hx.
    unfold in_sub_x_range. rewrite Hleft, Hright.
    exact Hx.
  - simpl in Hseg. destruct Hseg as [Hseg | Hseg].
    + subst seg.
      pose proof (Hmono a ltac:(now left)) as Ha.
      pose proof (x_monotone_segment_point_bounds a p Ha Hon) as Hx.
      assert (Hab : term a = init b).
      { apply (Hconn 0%nat a b); reflexivity. }
      assert (HconnTail : connected (b :: tail)).
      { intros i s1 s2 H1 H2.
        apply (Hconn (S i) s1 s2); simpl; assumption. }
      assert (HmonoTail : x_monotone_segs (b :: tail)).
      { intros t Ht. apply Hmono. now right. }
      pose proof (x_monotone_rect_x_bounds
                    (a :: b :: tail) ltac:(discriminate) Hconn Hmono)
        as [Hleft Hright].
      pose proof (connected_x_monotone_endpoints
                    (b :: tail) ltac:(discriminate)
                    HconnTail HmonoTail) as Htail.
      assert (Hlast :
          last_segment (a :: b :: tail) = last_segment (b :: tail)).
      { change (last_segment ([a] ++ b :: tail) = last_segment (b :: tail)).
        apply last_app_nonnil. discriminate. }
      unfold in_sub_x_range. rewrite Hleft, Hright.
      rewrite Hlast.
      change (fst (init a) <= fst p <=
              fst (term (last_segment (b :: tail)))).
      change (fst (init b) < fst (term (last_segment (b :: tail)))) in Htail.
      rewrite <- Hab in Htail. lra.
    + assert (Hab : term a = init b).
    { apply (Hconn 0%nat a b); reflexivity. }
    assert (HconnTail : connected (b :: tail)).
    { intros i s1 s2 H1 H2.
      apply (Hconn (S i) s1 s2); simpl; assumption. }
    assert (HmonoTail : x_monotone_segs (b :: tail)).
    { intros t Ht. apply Hmono. now right. }
    pose proof (x_monotone_rect_x_bounds
                  (a :: b :: tail) ltac:(discriminate) Hconn Hmono)
      as [Hleft Hright].
    unfold in_sub_x_range. rewrite Hleft, Hright.
    pose proof (IH b p HconnTail HmonoTail
                  (ex_intro _ seg (conj Hseg Hon))) as HpTail.
    pose proof (Hmono a ltac:(now left)) as Ha.
    pose proof (x_monotone_rect_x_bounds
                  (b :: tail) ltac:(discriminate)
                  HconnTail HmonoTail) as [HtailLeft HtailRight].
    unfold in_sub_x_range in HpTail.
    rewrite HtailLeft, HtailRight in HpTail.
    change (fst (init b) <= fst p <=
            fst (term (last_segment (b :: tail)))) in HpTail.
    assert (Hlast :
        last_segment (a :: b :: tail) = last_segment (b :: tail)).
    { change (last_segment ([a] ++ b :: tail) = last_segment (b :: tail)).
      apply last_app_nonnil. discriminate. }
    rewrite Hlast.
    change (fst (init a) <= fst p <=
            fst (term (last_segment (b :: tail)))).
    unfold x_monotone_seg, init_x, term_x in Ha.
    rewrite Hab in Ha. lra.
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

Lemma on_trace_above_sub_implies_strictly_above_at_x :
  forall sub p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    on_trace_above_sub sub p ->
    strictly_above_sub_at_x sub p.
Proof.
  intros sub p Hne Hconn Hmono
    [part [seg [p0 [q0 [Hdisjoint
      [Hp [Hp0 [Hq0 [Hx0 Hy0]]]]]]]]] q Hq Hx.
  destruct (disjoint_trace_sub_vertical_order_constant
              part seg sub Hne Hconn Hmono Hdisjoint
              p0 q0 p q Hp0 Hq0 Hx0 Hp Hq Hx)
    as [Habove _].
  now apply Habove.
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
  context_sub_x_monotone : x_monotone_segs sub;
  context_sparse : sparse_embedding (l ++ sub ++ r);
  context_whole_embedded :
    exists ds, embed_listDir ds (l ++ sub ++ r);
  context_extensions_disjoint : extensions_disjoint (l ++ sub ++ r)
}.

Lemma context_whole_connected : forall l sub r,
  ClassificationContext l sub r -> connected (l ++ sub ++ r).
Proof.
  intros l sub r Hctx.
  destruct (context_whole_embedded l sub r Hctx) as [ds Hembed].
  now apply (embed_listDir_connected ds (l ++ sub ++ r)).
Qed.

Lemma context_sub_connected : forall l sub r,
  ClassificationContext l sub r -> connected sub.
Proof.
  intros l sub r Hctx.
  apply connected_middle with (l := l) (r := r).
  now apply context_whole_connected.
Qed.

Lemma whole_nonempty : forall (l sub r : list Segment),
  sub <> [] -> l ++ sub ++ r <> [].
Proof.
  intros l sub r HsubNe Hnil.
  apply app_eq_nil in Hnil as [_ Hsubr].
  apply app_eq_nil in Hsubr as [Hsub _].
  exact (HsubNe Hsub).
Qed.

(* context の sparse 性と延長線非交差性から、曲線全体は開いている。 *)
Lemma context_whole_open : forall l sub r,
  ClassificationContext l sub r -> ~ close (l ++ sub ++ r).
Proof.
  intros l sub r Hctx.
  destruct (context_whole_embedded l sub r Hctx) as [ds Hembed].
  eapply sparse_extensions_open.
  - now apply whole_nonempty, context_sub_nonempty with (l := l) (r := r).
  - exact Hembed.
  - now apply context_sparse.
  - now apply context_extensions_disjoint.
Qed.

(* 仕様の結論で分類する点は sub 上の点または端点だけである。
   [p], [q], [e] は上下関係を示す幾何学的な証人であり分類しない。 *)
(* ----------------------------------------------------------------- *)
(*  分類器に要求する外部仕様                                       *)
(* ----------------------------------------------------------------- *)

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
    l <> [] ->
    forall p,
      onHead_extend_strict (l ++ sub ++ r) p ->
      rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub) ->
      classifier (init (hd_segment (l ++ sub ++ r))) = RegUp
      \/ classifier (init (hd_segment (l ++ sub ++ r))) = RegDown;

  (* strict 末尾延長線についても、その基点を固定しない。 *)
  classified_last_extension_at_sub_x :
    r <> [] ->
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
(*  端点間の順序制約と有限パス                                     *)
(* ----------------------------------------------------------------- *)

(* 通常の端点順序。セグメント本体と非隣接セグメント間の比較だけを含み、
   先頭・末尾の傾き保存や延長線には依存しない。 *)
Inductive endpoint_core_step
    (l sub r : list Segment) : Point -> Point -> Prop :=
  (* 同一セグメントでは、低い端点から高い端点へ領域順序を付ける。 *)
  | order_on_segment : forall seg p q,
      In seg (l ++ sub ++ r) ->
      endpoint_of_seg seg p ->
      endpoint_of_seg seg q ->
      snd p <= snd q ->
      endpoint_core_step l sub r p q
  (* x 範囲が重なる非隣接セグメント間では、低い端点から高い端点へ制約する。 *)
  | order_nonadjacent : forall i j s t ps pt,
      nth_error (l ++ sub ++ r) i = Some s ->
      nth_error (l ++ sub ++ r) j = Some t ->
      (S i < j \/ S j < i)%nat ->
      segment_x_ranges_overlap s t ->
      endpoint_of_seg s ps ->
      endpoint_of_seg t pt ->
      snd ps <= snd pt ->
      endpoint_core_step l sub r ps pt.

(* 先頭・末尾に固有の例外順序。傾き保存のための逆向き辺と、
   延長線を介した比較をここに隔離する。 *)
Inductive endpoint_end_step
    (l sub r : list Segment) : Point -> Point -> Prop :=
  (* 北向き・上に凸な先頭では、通常順序の逆も加えて両端を同じ領域にする。 *)
  | order_head_north_cx_reverse : forall hor,
      l <> [] ->
      embed (n, hor, cx) (hd_segment l) ->
      endpoint_end_step l sub r
        (term (hd_segment l)) (init (hd_segment l))
  (* 南向き・下に凸な先頭でも、始点傾き保存のため通常順序の逆を加える。 *)
  | order_head_south_cc_reverse : forall hor,
      l <> [] ->
      embed (s, hor, cc) (hd_segment l) ->
      endpoint_end_step l sub r
        (init (hd_segment l)) (term (hd_segment l))
  (* 北向き・下に凸な末尾では、終点傾き保存のため通常順序の逆を加える。 *)
  | order_last_north_cc_reverse : forall hor,
      r <> [] ->
      embed (n, hor, cc) (last_segment r) ->
      endpoint_end_step l sub r
        (term (last_segment r)) (init (last_segment r))
  (* 南向き・上に凸な末尾でも、通常順序の逆を加えて両端を同じ領域にする。 *)
  | order_last_south_cx_reverse : forall hor,
      r <> [] ->
      embed (s, hor, cx) (last_segment r) ->
      endpoint_end_step l sub r
        (init (last_segment r)) (term (last_segment r))
  (* 同じ x で先頭延長線が末尾延長線以下なら、先頭基点を末尾基点以下にする。 *)
  | order_head_last : forall ph pl,
      onHead_extend (l ++ sub ++ r) ph ->
      onLast_extend (l ++ sub ++ r) pl ->
      fst ph = fst pl ->
      snd ph <= snd pl ->
      endpoint_end_step l sub r
        (init (hd_segment (l ++ sub ++ r)))
        (term (last_segment (l ++ sub ++ r)))
  (* 同じ x で末尾延長線が先頭延長線以下なら、末尾基点を先頭基点以下にする。 *)
  | order_last_head : forall ph pl,
      onHead_extend (l ++ sub ++ r) ph ->
      onLast_extend (l ++ sub ++ r) pl ->
      fst ph = fst pl ->
      snd pl <= snd ph ->
      endpoint_end_step l sub r
        (term (last_segment (l ++ sub ++ r)))
        (init (hd_segment (l ++ sub ++ r)))
  (* 先頭延長線がセグメントより下なら、その基点をセグメントの各端点以下にする。 *)
  | order_head_below_segment : forall seg e q p,
      In seg (l ++ sub ++ r) ->
      onSegment seg e ->
      onHead_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      snd q <= snd e ->
      endpoint_of_seg seg p ->
      endpoint_end_step l sub r
        (init (hd_segment (l ++ sub ++ r))) p
  (* セグメントが先頭延長線より下なら、その各端点を先頭基点以下にする。 *)
  | order_segment_below_head : forall seg e q p,
      In seg (l ++ sub ++ r) ->
      onSegment seg e ->
      onHead_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      snd e <= snd q ->
      endpoint_of_seg seg p ->
      endpoint_end_step l sub r p
        (init (hd_segment (l ++ sub ++ r)))
  (* 末尾延長線がセグメントより下なら、その基点をセグメントの各端点以下にする。 *)
  | order_last_below_segment : forall seg e q p,
      In seg (l ++ sub ++ r) ->
      onSegment seg e ->
      onLast_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      snd q <= snd e ->
      endpoint_of_seg seg p ->
      endpoint_end_step l sub r
        (term (last_segment (l ++ sub ++ r))) p
  (* セグメントが末尾延長線より下なら、その各端点を末尾基点以下にする。 *)
  | order_segment_below_last : forall seg e q p,
      In seg (l ++ sub ++ r) ->
      onSegment seg e ->
      onLast_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      snd e <= snd q ->
      endpoint_of_seg seg p ->
      endpoint_end_step l sub r p
        (term (last_segment (l ++ sub ++ r))).

(* 全順序の一辺は、通常辺か先頭・末尾由来の例外辺のいずれかである。 *)
Inductive endpoint_order_step
    (l sub r : list Segment) : Point -> Point -> Prop :=
  | order_core_step : forall p q,
      endpoint_core_step l sub r p q ->
      endpoint_order_step l sub r p q
  | order_end_step : forall p q,
      endpoint_end_step l sub r p q ->
      endpoint_order_step l sub r p q.

Definition endpoint_order (l sub r : list Segment) : Point -> Point -> Prop :=
  clos_refl_trans Point (endpoint_order_step l sub r).

(* 幾何学的な帰納では、結合木を持つ [clos_refl_trans] よりも、先頭から
   一辺ずつ読めるこの有限パス表示を用いる。 *)
Definition endpoint_order_path
    (l sub r : list Segment) : Point -> Point -> Prop :=
  clos_refl_trans_1n Point (endpoint_order_step l sub r).

(* 例外辺を含まない一つの通常区間。例外辺の前後で保存する不変量を
   切り替える際の単位として用いる。 *)
Definition endpoint_core_path
    (l sub r : list Segment) : Point -> Point -> Prop :=
  clos_refl_trans_1n Point (endpoint_core_step l sub r).

(* 任意の順序経路を「通常区間の後に、例外辺と通常区間を反復する」形で保持する。
   各 [end] でのみ Head/Last 用の不変量を切り替えればよい。 *)
Inductive endpoint_factored_path
    (l sub r : list Segment) : Point -> Point -> Prop :=
  | factored_core : forall p q,
      endpoint_core_path l sub r p q ->
      endpoint_factored_path l sub r p q
  | factored_end : forall p before after q,
      endpoint_core_path l sub r p before ->
      endpoint_end_step l sub r before after ->
      endpoint_factored_path l sub r after q ->
      endpoint_factored_path l sub r p q.

Lemma endpoint_order_path_iff : forall l sub r p q,
  endpoint_order l sub r p q <-> endpoint_order_path l sub r p q.
Proof.
  intros l sub r p q.
  apply clos_rt_rt1n_iff.
Qed.

Lemma endpoint_order_path_trans : forall l sub r p q z,
  endpoint_order_path l sub r p q ->
  endpoint_order_path l sub r q z ->
  endpoint_order_path l sub r p z.
Proof.
  intros l sub r p q z Hpq Hqz.
  apply (proj1 (endpoint_order_path_iff l sub r p z)).
  eapply rt_trans.
  - now apply (proj2 (endpoint_order_path_iff l sub r p q)).
  - now apply (proj2 (endpoint_order_path_iff l sub r q z)).
Qed.

Lemma endpoint_order_path_is_factored : forall l sub r p q,
  endpoint_order_path l sub r p q ->
  endpoint_factored_path l sub r p q.
Proof.
  intros l sub r p q Hpath.
  induction Hpath as [p | p next q Hstep Htail IH].
  - apply factored_core.
    apply Stdlib.Relations.Relation_Operators.rt1n_refl.
  - destruct Hstep as [p next Hcore | p next Hend].
    + destruct IH as [next q Hpath | next before after q Hprefix Hend' Htail'].
      * apply factored_core.
        eapply Stdlib.Relations.Relation_Operators.rt1n_trans; eauto.
      * eapply factored_end.
        -- eapply Stdlib.Relations.Relation_Operators.rt1n_trans; eauto.
        -- exact Hend'.
        -- exact Htail'.
    + eapply factored_end with (before := p) (after := next).
      * apply Stdlib.Relations.Relation_Operators.rt1n_refl.
      * exact Hend.
      * exact IH.
Qed.

(* パスの始点が性質 [P] を持ち終点が持たないなら、[P] を初めて
   失う一辺がある。障壁を越える最初の局所比較を取り出すために使う。 *)
Lemma endpoint_order_path_first_exit :
  forall l sub r (P : Point -> Prop) p q,
    endpoint_order_path l sub r p q ->
    P p ->
    ~ P q ->
    exists before after,
      endpoint_order_path l sub r p before
      /\ endpoint_order_step l sub r before after
      /\ P before
      /\ ~ P after
      /\ endpoint_order_path l sub r after q.
Proof.
  intros l sub r P p q Hpath.
  induction Hpath as [p | p next q Hstep Htail IH].
  - intros Hp Hnp. contradiction.
  - intros Hp Hnq.
    destruct (classic (P next)) as [Hnext | Hnext].
    + destruct (IH Hnext Hnq)
        as [before [after [Hprefix [Hexit [Hbefore [Hafter Hsuffix]]]]]].
      exists before, after. split.
      * eapply (@Stdlib.Relations.Relation_Operators.rt1n_trans
                  Point (endpoint_order_step l sub r)
                  p next before); eauto.
      * repeat split; assumption.
    + exists p, next. split.
      * apply Stdlib.Relations.Relation_Operators.rt1n_refl.
      * repeat split; assumption.
Qed.

(* sub 外から sub 上へ至る有限パスには、sub へ初めて入る一辺がある。 *)
Lemma endpoint_order_path_first_sub_entry :
  forall l sub r p q,
    endpoint_order_path l sub r p q ->
    ~ onSegmentlist sub p ->
    onSegmentlist sub q ->
    exists before at_sub,
      endpoint_order_path l sub r p before
      /\ endpoint_order_step l sub r before at_sub
      /\ ~ onSegmentlist sub before
      /\ onSegmentlist sub at_sub
      /\ endpoint_order_path l sub r at_sub q.
Proof.
  intros l sub r p q Hpath Hp Hq.
  destruct (endpoint_order_path_first_exit
              l sub r (fun z => ~ onSegmentlist sub z)
              p q Hpath Hp ltac:(tauto))
    as [before [at_sub [Hprefix [Hstep [Hbefore [Hat Hsuffix]]]]]].
  exists before, at_sub. repeat split; try assumption.
  now apply NNPP.
Qed.

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
   \/ (l <> []
       /\ p = init (hd_segment (l ++ sub ++ r))
       /\ exists q z,
            onHead_extend_strict (l ++ sub ++ r) q
            /\ onSegmentlist sub z
            /\ fst q = fst z
            /\ snd z < snd q)
   \/ (r <> []
       /\ p = term (last_segment (l ++ sub ++ r))
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
   \/ (l <> []
       /\ p = init (hd_segment (l ++ sub ++ r))
       /\ exists q z,
            onHead_extend_strict (l ++ sub ++ r) q
            /\ onSegmentlist sub z
            /\ fst q = fst z
            /\ snd q < snd z)
   \/ (r <> []
       /\ p = term (last_segment (l ++ sub ++ r))
       /\ exists q z,
            onLast_extend_strict (l ++ sub ++ r) q
            /\ onSegmentlist sub z
            /\ fst q = fst z
            /\ snd q < snd z)).

(* ----------------------------------------------------------------- *)
(*  Up 経路を sub より上に保つための不変量                       *)
(* ----------------------------------------------------------------- *)

Definition sub_left_anchor (sub : list Segment) : Point :=
  init (hd_segment sub).

Definition sub_right_anchor (sub : list Segment) : Point :=
  term (last_segment sub).

(* sub と同じ x にあり、その高さ以下にある点。等号を含めることで
   sub 上への再衝突も同時に危険点として扱う。 *)
Definition at_or_below_sub_at_x
    (sub : list Segment) (p : Point) : Prop :=
  exists q,
    onSegmentlist sub q
    /\ fst p = fst q
    /\ snd p <= snd q.

Definition unsafe_up_point
    (sub : list Segment) (p : Point) : Prop :=
  in_sub_x_range sub p /\ at_or_below_sub_at_x sub p.

(* 障壁として選んだ trace が、先頭側と末尾側のどちらかを記録する。
   Segment の値だけでは、同じ値の重複出現を区別できない。 *)
Inductive BarrierEnd : Type := BarrierHead | BarrierLast.

Definition barrier_segment (side : BarrierEnd) (whole : list Segment) : Segment :=
  match side with
  | BarrierHead => hd_segment whole
  | BarrierLast => last_segment whole
  end.

Definition on_barrier_trace
    (side : BarrierEnd) (whole : list Segment) (p : Point) : Prop :=
  match side with
  | BarrierHead => onHeadSegment (hd_segment whole) p
  | BarrierLast => onLastSegment (last_segment whole) p
  end.

Lemma on_barrier_trace_onExtend : forall side whole p,
  whole <> [] ->
  on_barrier_trace side whole p ->
  onExtendSegment whole (barrier_segment side whole) p.
Proof.
  intros side whole p Hwhole Htrace.
  destruct side; cbn in *.
  - destruct whole as [|head tail]; [contradiction|].
    now apply OnSegHead.
  - now apply OnSegLast.
Qed.

Lemma barrier_segment_In : forall side whole,
  whole <> [] -> In (barrier_segment side whole) whole.
Proof.
  intros side whole Hwhole. destruct side; cbn.
  - destruct whole as [|head tail]; [contradiction|]. now left.
  - now apply last_In.
Qed.

(* x が増える向きに y も厳密に増える、選択済み end trace。 *)
Definition right_rising_barrier
    (side : BarrierEnd) (whole : list Segment) : Prop :=
  forall p q,
    on_barrier_trace side whole p ->
    on_barrier_trace side whole q ->
    (fst p < fst q <-> snd p < snd q).

(* 右側の障壁は左側と双対で、x が増えると y が厳密に下がる。 *)
Definition right_falling_barrier
    (side : BarrierEnd) (whole : list Segment) : Prop :=
  forall p q,
    on_barrier_trace side whole p ->
    on_barrier_trace side whole q ->
    (fst p < fst q <-> snd q < snd p).

(* 点より真に上で init sub まで続く左側境界。下端を開けることで、
   通常点と境界自身に属する例外端点を同じ形で扱う。 *)
Definition left_barrier_core
    (side : BarrierEnd) (l sub r : list Segment) (p : Point) : Prop :=
  let whole := l ++ sub ++ r in
  let left := sub_left_anchor sub in
  whole <> []
  /\ right_rising_barrier side whole
  /\ fst p < fst left
  /\ snd p < snd left
  /\ (forall y,
        snd p < y <= snd left ->
        exists x,
          fst p < x < fst left
          /\ on_barrier_trace side whole (x, y)).

Definition right_barrier_core
    (side : BarrierEnd) (l sub r : list Segment) (p : Point) : Prop :=
  let whole := l ++ sub ++ r in
  let right := sub_right_anchor sub in
  whole <> []
  /\ right_falling_barrier side whole
  /\ fst right < fst p
  /\ snd p < snd right
  /\ (forall y,
        snd p < y <= snd right ->
        exists x,
          fst right < x < fst p
          /\ on_barrier_trace side whole (x, y)).

(* 通常点では、点と同じ高さにも境界がその内側に実在する。 *)
Definition left_barrier_at_level
    (side : BarrierEnd) (l sub r : list Segment) (p : Point) : Prop :=
  exists x,
    fst p < x < fst (sub_left_anchor sub)
    /\ on_barrier_trace side (l ++ sub ++ r) (x, snd p).

Definition right_barrier_at_level
    (side : BarrierEnd) (l sub r : list Segment) (p : Point) : Prop :=
  exists x,
    fst (sub_right_anchor sub) < x < fst p
    /\ on_barrier_trace side (l ++ sub ++ r) (x, snd p).

(* 従来の通常境界は、開いた core と下端高さの証人の組である。 *)
Definition left_vertical_guard_to_init
    (l sub r : list Segment) (p : Point) : Prop :=
  exists side,
    left_barrier_core side l sub r p
    /\ left_barrier_at_level side l sub r p.

(* 右側では term sub まで同じ障壁を張る。 *)
Definition right_vertical_guard_to_term
    (l sub r : list Segment) (p : Point) : Prop :=
  exists side,
    right_barrier_core side l sub r p
    /\ right_barrier_at_level side l sub r p.

Lemma left_barrier_closed_span : forall side l sub r p,
  left_barrier_core side l sub r p ->
  left_barrier_at_level side l sub r p ->
  forall y,
    snd p <= y <= snd (sub_left_anchor sub) ->
    exists x,
      fst p < x < fst (sub_left_anchor sub)
      /\ on_barrier_trace side (l ++ sub ++ r) (x, y).
Proof.
  intros side l sub r p Hcore Hlevel y Hy.
  unfold left_barrier_core in Hcore. cbn in Hcore.
  destruct Hcore as [_ [_ [_ [_ Hopen]]]].
  destruct (Req_dec y (snd p)) as [-> | Hneq].
  - exact Hlevel.
  - apply Hopen. lra.
Qed.

Lemma right_barrier_closed_span : forall side l sub r p,
  right_barrier_core side l sub r p ->
  right_barrier_at_level side l sub r p ->
  forall y,
    snd p <= y <= snd (sub_right_anchor sub) ->
    exists x,
      fst (sub_right_anchor sub) < x < fst p
      /\ on_barrier_trace side (l ++ sub ++ r) (x, y).
Proof.
  intros side l sub r p Hcore Hlevel y Hy.
  unfold right_barrier_core in Hcore. cbn in Hcore.
  destruct Hcore as [_ [_ [_ [_ Hopen]]]].
  destruct (Req_dec y (snd p)) as [-> | Hneq].
  - exact Hlevel.
  - apply Hopen. lra.
Qed.

(* [p] の strict guard を構成するまさに同じ障壁に [q] が接触する。
   障壁の識別を失うと、無関係な別の障壁を選べてしまう。 *)
Definition left_strict_guard_contact
    (l sub r : list Segment) (p q : Point) : Prop :=
  let whole := l ++ sub ++ r in
  let left := sub_left_anchor sub in
  exists side,
    whole <> []
    /\ right_rising_barrier side whole
    /\ snd p < snd left
    /\ (forall y,
          snd p <= y <= snd left ->
          exists x,
            fst p < x < fst left
            /\ on_barrier_trace side whole (x, y))
    /\ on_barrier_trace side whole q.

Definition right_strict_guard_contact
    (l sub r : list Segment) (p q : Point) : Prop :=
  let whole := l ++ sub ++ r in
  let right := sub_right_anchor sub in
  exists side,
    whole <> []
    /\ right_falling_barrier side whole
    /\ snd p < snd right
    /\ (forall y,
          snd p <= y <= snd right ->
          exists x,
            fst right < x < fst p
            /\ on_barrier_trace side whole (x, y))
    /\ on_barrier_trace side whole q.

(* 同一セグメントの上向き通常辺では、到達点は同じ障壁の左に
   残るか、障壁自身に到達する。右側へ突き抜けると自己交差になる。 *)
Lemma left_guard_preserved_by_same_segment_or_contact :
  forall l sub r seg p q,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    snd p <= snd q ->
    left_vertical_guard_to_init l sub r p ->
    fst q < fst (sub_left_anchor sub) ->
    snd q < snd (sub_left_anchor sub) ->
    left_vertical_guard_to_init l sub r q
    \/ left_strict_guard_contact l sub r p q.
Proof.
  intros l sub r seg [xp yp] [xq yq]
    Hctx Hseg Hp Hq Hy Hguard Hqx Hqy.
  unfold left_vertical_guard_to_init in Hguard |- *.
  destruct Hguard as [side [Hcore Hlevel]].
  pose proof (left_barrier_closed_span side l sub r (xp, yp)
                Hcore Hlevel) as Hspan.
  unfold left_barrier_core in Hcore. cbn in Hcore.
  destruct Hcore as [HbarWhole [Hrising [HpxLeft [HpTop Hopen]]]].
  cbn in *.
  destruct (Hspan yp ltac:(lra)) as [xbp [[Hpxbp HbpLeft] Hbp]].
  destruct (Hspan yq ltac:(lra)) as [xbq [[Hpxbq HbqLeft] Hbq]].
  assert (Hwhole : l ++ sub ++ r <> []).
  { now apply whole_nonempty, context_sub_nonempty with (l := l) (r := r). }
  assert (Hpseg : onExtendSegment (l ++ sub ++ r) seg (xp, yp)).
  { apply OnSegMid; [exact Hwhole | exact Hseg |].
    destruct Hp as [-> | ->]; [apply onInit | apply onTerm]. }
  assert (Hqseg : onExtendSegment (l ++ sub ++ r) seg (xq, yq)).
  { apply OnSegMid; [exact Hwhole | exact Hseg |].
    destruct Hq as [-> | ->]; [apply onInit | apply onTerm]. }
  destruct (total_order_T xq xbq) as [[HqLeft | HqOn] | HqRight].
  - left. exists side. split.
    + unfold left_barrier_core. cbn.
      split; [exact HbarWhole |].
      split; [exact Hrising |].
      split; [exact Hqx |].
      split; [exact Hqy |].
      intros y HyRange.
      destruct (Hspan y ltac:(lra)) as [xb [[Hpxb HbLeft] Hb]].
      assert (Hbqxb : xbq <= xb).
      { destruct (Rle_dec xbq xb) as [Hle | Hnle]; [exact Hle |].
        assert (Hxb : xb < xbq) by lra.
        pose proof
          (proj1 (Hrising (xb, y) (xbq, yq) Hb Hbq) Hxb) as Hyy.
        cbn in Hyy. lra. }
      exists xb. split; [lra | exact Hb].
    + unfold left_barrier_at_level. cbn.
      exists xbq. split; [lra | exact Hbq].
  - right. unfold left_strict_guard_contact. cbn.
    exists side. split; [exact HbarWhole |].
    split; [exact Hrising |].
    split; [exact HpTop |].
    split; [exact Hspan |].
    replace (xq, yq) with (xbq, yq) by now rewrite HqOn.
    exact Hbq.
  - exfalso. apply (context_whole_open l sub r Hctx).
    assert (Hbarrier : In (barrier_segment side (l ++ sub ++ r))
                           (l ++ sub ++ r))
      by now apply barrier_segment_In.
    assert (HbpExt : onExtendSegment (l ++ sub ++ r)
                       (barrier_segment side (l ++ sub ++ r)) (xbp, yp))
      by now apply on_barrier_trace_onExtend.
    assert (HbqExt : onExtendSegment (l ++ sub ++ r)
                       (barrier_segment side (l ++ sub ++ r)) (xbq, yq))
      by now apply on_barrier_trace_onExtend.
    eapply x_cross_v with
      (s1 := seg) (s2 := barrier_segment side (l ++ sub ++ r))
      (ya := yp) (yb := yq)
      (x1a := xp) (x1b := xq)
      (x2a := xbp) (x2b := xbq); eauto.
    nra.
Qed.

(* 右側でも、同一セグメントは同じ障壁の右に残るか、
   障壁上の端点に到達する。左へ突き抜けると自己交差になる。 *)
Lemma right_guard_preserved_by_same_segment_or_contact :
  forall l sub r seg p q,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    snd p <= snd q ->
    right_vertical_guard_to_term l sub r p ->
    fst (sub_right_anchor sub) < fst q ->
    snd q < snd (sub_right_anchor sub) ->
    right_vertical_guard_to_term l sub r q
    \/ right_strict_guard_contact l sub r p q.
Proof.
  intros l sub r seg [xp yp] [xq yq]
    Hctx Hseg Hp Hq Hy Hguard Hqx Hqy.
  unfold right_vertical_guard_to_term in Hguard |- *.
  destruct Hguard as [side [Hcore Hlevel]].
  pose proof (right_barrier_closed_span side l sub r (xp, yp)
                Hcore Hlevel) as Hspan.
  unfold right_barrier_core in Hcore. cbn in Hcore.
  destruct Hcore as [HbarWhole [Hfalling [HrightPx [HpTop Hopen]]]].
  cbn in *.
  destruct (Hspan yp ltac:(lra)) as [xbp [[HbpRight HbpLeft] Hbp]].
  destruct (Hspan yq ltac:(lra)) as [xbq [[HbqRight HbqLeft] Hbq]].
  assert (Hwhole : l ++ sub ++ r <> []).
  { now apply whole_nonempty, context_sub_nonempty with (l := l) (r := r). }
  assert (Hpseg : onExtendSegment (l ++ sub ++ r) seg (xp, yp)).
  { apply OnSegMid; [exact Hwhole | exact Hseg |].
    destruct Hp as [-> | ->]; [apply onInit | apply onTerm]. }
  assert (Hqseg : onExtendSegment (l ++ sub ++ r) seg (xq, yq)).
  { apply OnSegMid; [exact Hwhole | exact Hseg |].
    destruct Hq as [-> | ->]; [apply onInit | apply onTerm]. }
  destruct (total_order_T xbq xq) as [[HqRight | HqOn] | HqLeft].
  - left. exists side. split.
    + unfold right_barrier_core. cbn.
      split; [exact HbarWhole |].
      split; [exact Hfalling |].
      split; [exact Hqx |].
      split; [exact Hqy |].
      intros y HyRange.
      destruct (Hspan y ltac:(lra)) as [xb [[HbRight HbLeft] Hb]].
      assert (Hxbq : xb <= xbq).
      { destruct (Rle_dec xb xbq) as [Hle | Hnle]; [exact Hle |].
        assert (Hlt : xbq < xb) by lra.
        pose proof
          (proj1 (Hfalling (xbq, yq) (xb, y) Hbq Hb) Hlt) as Hyy.
        cbn in Hyy. lra. }
      exists xb. split; [lra | exact Hb].
    + unfold right_barrier_at_level. cbn.
      exists xbq. split; [lra | exact Hbq].
  - right. unfold right_strict_guard_contact. cbn.
    exists side. split; [exact HbarWhole |].
    split; [exact Hfalling |].
    split; [exact HpTop |].
    split; [exact Hspan |].
    replace (xq, yq) with (xbq, yq) by now rewrite HqOn.
    exact Hbq.
  - exfalso. apply (context_whole_open l sub r Hctx).
    assert (Hbarrier : In (barrier_segment side (l ++ sub ++ r))
                           (l ++ sub ++ r))
      by now apply barrier_segment_In.
    assert (HbpExt : onExtendSegment (l ++ sub ++ r)
                       (barrier_segment side (l ++ sub ++ r)) (xbp, yp))
      by now apply on_barrier_trace_onExtend.
    assert (HbqExt : onExtendSegment (l ++ sub ++ r)
                       (barrier_segment side (l ++ sub ++ r)) (xbq, yq))
      by now apply on_barrier_trace_onExtend.
    eapply x_cross_v with
      (s1 := seg) (s2 := barrier_segment side (l ++ sub ++ r))
      (ya := yp) (yb := yq)
      (x1a := xp) (x1b := xq)
      (x2a := xbp) (x2b := xbq); eauto.
    nra.
Qed.

(* 下端自身が境界上にある seed は、sub より上を通る先頭・末尾
   延長線の基点である。境界の上側部分は certificate で別に保持する。 *)
Definition extension_up_seed
    (l sub r : list Segment) (p : Point) : Prop :=
  (l <> []
   /\ p = init (hd_segment (l ++ sub ++ r))
   /\ exists q z,
        onHead_extend_strict (l ++ sub ++ r) q
        /\ onSegmentlist sub z
        /\ fst q = fst z
        /\ snd z < snd q)
  \/
  (r <> []
   /\ p = term (last_segment (l ++ sub ++ r))
   /\ exists q z,
        onLast_extend_strict (l ++ sub ++ r) q
        /\ onSegmentlist sub z
        /\ fst q = fst z
        /\ snd z < snd q).

(* 延長線 seed が先頭・末尾のどちらを障壁として使うかも記録する。 *)
Definition barrier_extension_seed
    (l sub r : list Segment) (side : BarrierEnd) (p : Point) : Prop :=
  match side with
  | BarrierHead =>
      l <> []
      /\ p = init (hd_segment (l ++ sub ++ r))
      /\ exists q z,
           onHead_extend_strict (l ++ sub ++ r) q
           /\ onSegmentlist sub z
           /\ fst q = fst z
           /\ snd z < snd q
  | BarrierLast =>
      r <> []
      /\ p = term (last_segment (l ++ sub ++ r))
      /\ exists q z,
           onLast_extend_strict (l ++ sub ++ r) q
           /\ onSegmentlist sub z
           /\ fst q = fst z
           /\ snd z < snd q
  end.

Lemma barrier_extension_seed_is_extension_up_seed : forall l sub r side p,
  barrier_extension_seed l sub r side p ->
  extension_up_seed l sub r p.
Proof.
  intros l sub r [] p Hseed; [left | right]; exact Hseed.
Qed.

(* 傾き保存用の逆向き end-step が、Up を低い端点へ移す四つの場合。
   単に先頭・末尾の端点であるだけでは例外にしない。 *)
Definition reverse_end_target
    (l sub r : list Segment) (p : Point) : Prop :=
  (exists hor,
      l <> []
      /\ embed (n, hor, cx) (hd_segment l)
      /\ p = init (hd_segment l))
  \/ (exists hor,
      l <> []
      /\ embed (s, hor, cc) (hd_segment l)
      /\ p = term (hd_segment l))
  \/ (exists hor,
      r <> []
      /\ embed (n, hor, cc) (last_segment r)
      /\ p = init (last_segment r))
  \/ (exists hor,
      r <> []
      /\ embed (s, hor, cx) (last_segment r)
      /\ p = term (last_segment r)).

(* 延長線 seed と逆向き end-step の到達点をまとめる幾何補助述語。
   証明書本体ではこれだけに頼らず、下の帰納型に生成履歴を保存する。 *)
Definition barrier_exception
    (l sub r : list Segment) (p : Point) : Prop :=
  extension_up_seed l sub r p \/ reverse_end_target l sub r p.

(* 経路全体を禁止するのではなく、特殊点から sub 以下へ出る直接の一辺
   だけを拒む。従って最終目標の言い換えにはなっていない。 *)
Definition locally_blocks_unsafe_up
    (l sub r : list Segment) (p : Point) : Prop :=
  forall q,
    endpoint_order_step l sub r p q ->
    ~ unsafe_up_point sub q.

(* 障壁を作る逆向き end-step は四種類だけである。向きだけでなく、
   どの端点からどの端点へ下ったかも記録しておく。 *)
Inductive barrier_reverse_step
    (l sub r : list Segment) : BarrierEnd -> Point -> Point -> Prop :=
  | barrier_reverse_head_north_cx : forall hor,
      l <> [] ->
      embed (n, hor, cx) (hd_segment l) ->
      barrier_reverse_step l sub r BarrierHead
        (term (hd_segment l)) (init (hd_segment l))
  | barrier_reverse_head_south_cc : forall hor,
      l <> [] ->
      embed (s, hor, cc) (hd_segment l) ->
      barrier_reverse_step l sub r BarrierHead
        (init (hd_segment l)) (term (hd_segment l))
  | barrier_reverse_last_north_cc : forall hor,
      r <> [] ->
      embed (n, hor, cc) (last_segment r) ->
      barrier_reverse_step l sub r BarrierLast
        (term (last_segment r)) (init (last_segment r))
  | barrier_reverse_last_south_cx : forall hor,
      r <> [] ->
      embed (s, hor, cx) (last_segment r) ->
      barrier_reverse_step l sub r BarrierLast
        (init (last_segment r)) (term (last_segment r)).

Lemma barrier_reverse_step_has_reverse_target : forall l sub r side previous p,
  barrier_reverse_step l sub r side previous p ->
  reverse_end_target l sub r p.
Proof.
  intros l sub r side previous p Hstep. destruct Hstep.
  - left. exists hor. repeat split; assumption.
  - right. left. exists hor. repeat split; assumption.
  - right. right. left. exists hor. repeat split; assumption.
  - do 3 right. exists hor. repeat split; assumption.
Qed.

(* 逆向き step の到達点と異なる同じ障壁セグメントの端点は、
   step 前に証明書を持っていた端点そのものである。 *)
Lemma barrier_reverse_step_other_endpoint : forall l sub r side previous p seg q,
  barrier_reverse_step l sub r side previous p ->
  seg = barrier_segment side (l ++ sub ++ r) ->
  endpoint_of_seg seg p ->
  endpoint_of_seg seg q ->
  p <> q ->
  q = previous.
Proof.
  intros l sub r side previous p seg q Hstep Hseg _ Hq Hneq.
    destruct Hstep as
      [hor Hl Hembed | hor Hl Hembed | hor Hr Hembed | hor Hr Hembed].
    - destruct l as [|a l']; [contradiction |]. cbn in Hseg |- *.
      subst seg. destruct Hq as [Hq | Hq].
      + exfalso. apply Hneq. exact (eq_sym Hq).
      + exact Hq.
  - destruct l as [|a l']; [contradiction |]. cbn in Hseg |- *.
    subst seg. destruct Hq as [Hq | Hq].
      + exact Hq.
    + exfalso. apply Hneq. exact (eq_sym Hq).
    - assert (Hlast : last_segment (l ++ sub ++ r) = last_segment r).
      { rewrite (last_app_nonnil l (sub ++ r)).
        - apply last_app_nonnil. exact Hr.
        - intros Hnil. apply app_eq_nil in Hnil. tauto. }
      cbn in Hseg. rewrite Hlast in Hseg. subst seg. destruct Hq as [Hq | Hq].
      + exfalso. apply Hneq. exact (eq_sym Hq).
      + exact Hq.
    - assert (Hlast : last_segment (l ++ sub ++ r) = last_segment r).
      { rewrite (last_app_nonnil l (sub ++ r)).
        - apply last_app_nonnil. exact Hr.
        - intros Hnil. apply app_eq_nil in Hnil. tauto. }
      cbn in Hseg. rewrite Hlast in Hseg. subst seg. destruct Hq as [Hq | Hq].
      + exact Hq.
    + exfalso. apply Hneq. exact (eq_sym Hq).
Qed.

(* 左右の証明書は、通常の同高さ障壁、延長線 seed、逆向き step の
   いずれから作られたかを保持する。逆向きの場合は移動前の証明書も保存する。 *)
Inductive left_up_certificate
    (l sub r : list Segment) : Point -> Prop :=
  | left_certificate_at_level : forall side p,
      left_barrier_core side l sub r p ->
      left_barrier_at_level side l sub r p ->
      left_up_certificate l sub r p
  | left_certificate_extension_seed : forall side p,
      left_barrier_core side l sub r p ->
      barrier_extension_seed l sub r side p ->
      locally_blocks_unsafe_up l sub r p ->
      on_barrier_trace side (l ++ sub ++ r) p ->
      left_up_certificate l sub r p
  | left_certificate_reverse_step : forall side p previous,
      left_barrier_core side l sub r p ->
      barrier_reverse_step l sub r side previous p ->
      left_up_certificate l sub r previous ->
      locally_blocks_unsafe_up l sub r p ->
      on_barrier_trace side (l ++ sub ++ r) p ->
      left_up_certificate l sub r p.

Inductive right_up_certificate
    (l sub r : list Segment) : Point -> Prop :=
  | right_certificate_at_level : forall side p,
      right_barrier_core side l sub r p ->
      right_barrier_at_level side l sub r p ->
      right_up_certificate l sub r p
  | right_certificate_extension_seed : forall side p,
      right_barrier_core side l sub r p ->
      barrier_extension_seed l sub r side p ->
      locally_blocks_unsafe_up l sub r p ->
      on_barrier_trace side (l ++ sub ++ r) p ->
      right_up_certificate l sub r p
  | right_certificate_reverse_step : forall side p previous,
      right_barrier_core side l sub r p ->
      barrier_reverse_step l sub r side previous p ->
      right_up_certificate l sub r previous ->
      locally_blocks_unsafe_up l sub r p ->
      on_barrier_trace side (l ++ sub ++ r) p ->
      right_up_certificate l sub r p.

(* 左証明書に記録された barrier core から、その点が左 anchor の
   真に左下にあることを取り出す。 *)
Lemma left_up_certificate_position : forall l sub r p,
  left_up_certificate l sub r p ->
  fst p < fst (sub_left_anchor sub)
  /\ snd p < snd (sub_left_anchor sub).
Proof.
  intros l sub r p Hcertificate.
  destruct Hcertificate as
    [side p Hcore Hlevel
    | side p Hcore Hseed Hblocks Htrace
    | side p previous Hcore Hreverse Hprevious Hblocks Htrace];
    unfold left_barrier_core in Hcore; cbn in Hcore; tauto.
Qed.

(* 右証明書についても、その点が右 anchor の真に右下にあることは
   barrier core 自体に保存されている。 *)
Lemma right_up_certificate_position : forall l sub r p,
  right_up_certificate l sub r p ->
  fst (sub_right_anchor sub) < fst p
  /\ snd p < snd (sub_right_anchor sub).
Proof.
  intros l sub r p Hcertificate.
  destruct Hcertificate as
    [side p Hcore Hlevel
    | side p Hcore Hseed Hblocks Htrace
    | side p previous Hcore Hreverse Hprevious Hblocks Htrace];
    unfold right_barrier_core in Hcore; cbn in Hcore; tauto.
Qed.

(* 中央では欲しい結論そのものを保つ。左右では同じ open core を持ち、
   下端だけを通常境界点または将来の境界となる例外端点に分ける。 *)
Definition up_path_invariant
    (l sub r : list Segment) (p : Point) : Prop :=
  (in_sub_x_range sub p -> strictly_above_sub_at_x sub p)
  /\ (fst p < fst (sub_left_anchor sub) ->
      snd p < snd (sub_left_anchor sub) ->
      left_up_certificate l sub r p)
  /\ (fst (sub_right_anchor sub) < fst p ->
      snd p < snd (sub_right_anchor sub) ->
      right_up_certificate l sub r p).

(* ----------------------------------------------------------------- *)
(*  障壁 trace とセグメントの基礎幾何                              *)
(* ----------------------------------------------------------------- *)

Lemma right_rising_barrier_same_height_unique : forall side whole p q,
  right_rising_barrier side whole ->
  on_barrier_trace side whole p ->
  on_barrier_trace side whole q ->
  snd p = snd q ->
  p = q.
Proof.
  intros side whole [xp yp] [xq yq] Hrising Hp Hq Hy.
  simpl in Hy. subst yq.
  assert (Hx : xp = xq).
  { destruct (total_order_T xp xq) as [[Hlt | Heq] | Hgt]; [|exact Heq|].
    - pose proof (proj1 (Hrising (xp, yp) (xq, yp) Hp Hq) Hlt).
      simpl in H. lra.
    - pose proof (proj1 (Hrising (xq, yp) (xp, yp) Hq Hp) Hgt).
      simpl in H. lra. }
  now subst xq.
Qed.

Lemma right_falling_barrier_same_height_unique : forall side whole p q,
  right_falling_barrier side whole ->
  on_barrier_trace side whole p ->
  on_barrier_trace side whole q ->
  snd p = snd q ->
  p = q.
Proof.
  intros side whole [xp yp] [xq yq] Hfalling Hp Hq Hy.
  simpl in Hy. subst yq.
  assert (Hx : xp = xq).
  { destruct (total_order_T xp xq) as [[Hlt | Heq] | Hgt]; [|exact Heq|].
    - pose proof (proj1 (Hfalling (xp, yp) (xq, yp) Hp Hq) Hlt).
      simpl in H. lra.
    - pose proof (proj1 (Hfalling (xq, yp) (xp, yp) Hq Hp) Hgt).
      simpl in H. lra. }
  now subst xq.
Qed.

(* 埋め込まれた先頭 trace は、セグメント本体と始点側延長を合わせても、
   終点を越えて垂直方向へ戻らない。 *)
Lemma embedded_head_trace_vertical_bound : forall seg v h c p,
  embed (v, h, c) seg ->
  onHeadSegment seg p ->
  match v with
  | n => snd p <= snd (term seg)
  | s => snd (term seg) <= snd p
  end.
Proof.
  intros seg v h c [x y] Hembed [t [Ht <-]].
  destruct (Rle_dec 0 t) as [Ht0 | Ht0].
  - assert (Hon : onSegment seg (point seg t)).
    { exists t. split; [lra | reflexivity]. }
    destruct v.
    + assert (Hon' : onSegment seg
      (fst (point seg t), snd (point seg t))).
      { replace (fst (point seg t), snd (point seg t)) with (point seg t)
          by apply surjective_pairing. exact Hon. }
      exact (proj2 (n_onseg_relation seg h c
                      (fst (point seg t)) (snd (point seg t)) Hembed Hon')).
    + assert (Hon' : onSegment seg
      (fst (point seg t), snd (point seg t))).
      { replace (fst (point seg t), snd (point seg t)) with (point seg t)
          by apply surjective_pairing. exact Hon. }
      exact (proj1 (s_onseg_relation seg h c
                      (fst (point seg t)) (snd (point seg t)) Hembed Hon')).
  - assert (Hhead : onHead seg (point seg t)).
    { exists t. split; [lra | reflexivity]. }
    destruct v.
    + pose proof (north_head_extension_bounds seg h c (point seg t)
                    Hembed Hhead) as Hext.
      pose proof (n_end_relation seg h c Hembed) as Hend. lra.
    + pose proof (south_head_extension_bounds seg h c (point seg t)
                    Hembed Hhead) as Hext.
      pose proof (s_end_relation seg h c Hembed) as Hend. lra.
Qed.

Lemma embedded_head_trace_horizontal_bound : forall seg v h c p,
  embed (v, h, c) seg ->
  onHeadSegment seg p ->
  match h with
  | e => fst p <= fst (term seg)
  | w => fst (term seg) <= fst p
  end.
Proof.
  intros seg v h c [x y] Hembed [t [Ht <-]].
  destruct (Rle_dec 0 t) as [Ht0 | Ht0].
  - assert (Hon : onSegment seg (point seg t)).
    { exists t. split; [lra | reflexivity]. }
    destruct h.
    + assert (Hon' : onSegment seg
          (fst (point seg t), snd (point seg t))).
      { replace (fst (point seg t), snd (point seg t)) with (point seg t)
          by apply surjective_pairing. exact Hon. }
      exact (proj2 (e_onseg_relation seg v c
                      (fst (point seg t)) (snd (point seg t)) Hembed Hon')).
    + assert (Hon' : onSegment seg
          (fst (point seg t), snd (point seg t))).
      { replace (fst (point seg t), snd (point seg t)) with (point seg t)
          by apply surjective_pairing. exact Hon. }
      exact (proj1 (w_onseg_relation seg v c
                      (fst (point seg t)) (snd (point seg t)) Hembed Hon')).
  - assert (Hhead : onHead seg (point seg t)).
    { exists t. split; [lra | reflexivity]. }
    destruct h.
    + pose proof (east_head_extension_bounds seg v c (point seg t)
                    Hembed Hhead).
      pose proof (e_end_relation seg v c Hembed). lra.
    + pose proof (west_head_extension_bounds seg v c (point seg t)
                    Hembed Hhead).
      pose proof (w_end_relation seg v c Hembed). lra.
Qed.

(* 南向き先頭 trace で終点と同じ高さを取る点は終点自身だけである。 *)
Lemma south_head_trace_at_term_y : forall seg h c p,
  embed (s, h, c) seg ->
  onHeadSegment seg p ->
  snd p = snd (term seg) ->
  p = term seg.
Proof.
  intros seg h c [x y] Hembed [t [Ht Hpoint]] Hy.
  cbn in Hy.
  subst y.
  destruct (Rle_dec 0 t) as [Ht0 | Ht0].
  - apply on_segment_term_from_y.
    exists t. split; [lra | exact Hpoint].
    reflexivity.
  - assert (Hhead : onHead seg (x, snd (term seg))).
    { exists t. split; [lra | exact Hpoint]. }
    pose proof (south_head_extension_bounds seg h c
                  (x, snd (term seg)) Hembed Hhead) as Hext.
    pose proof (s_end_relation seg h c Hembed) as Hend. cbn in Hext. lra.
Qed.

(* 先頭 trace が一つのセグメントの端点対を下から上へ横切り、その
   一方の端点に触れることはない。同一・隣接・非隣接出現をそれぞれ
   単射性、接続方向、sparse 性で処理する幾何補題である。 *)
Lemma head_trace_cannot_straddle_segment_endpoint :
  forall l sub r seg p q below above,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    onHeadSegment (hd_segment (l ++ sub ++ r)) below ->
    onHeadSegment (hd_segment (l ++ sub ++ r)) q ->
    onHeadSegment (hd_segment (l ++ sub ++ r)) above ->
    snd below = snd p ->
    fst p <> fst below ->
    snd below < snd q ->
    snd q < snd above ->
    False.
Proof.
  intros l sub r seg p q below above Hctx Hseg Hp Hq
    Hbelow HqHead Habove Hbelowp Hpx Hbelowq Hqabove.
  set (whole := l ++ sub ++ r) in *.
  assert (Hwhole : whole <> []).
  { unfold whole. now apply whole_nonempty, context_sub_nonempty
      with (l := l) (r := r). }
  assert (HheadNth : nth_error whole 0 = Some (hd_segment whole)).
  { destruct whole as [|head tail]; [contradiction | reflexivity]. }
  destruct (context_whole_embedded l sub r Hctx)
    as [ds [sc [_ Hembed]]].
  change (embed_scurve sc whole) in Hembed.
  destruct (embed_scurve_nth_embed sc whole Hembed 0
              (hd_segment whole) HheadNth)
    as [[[v h] c] [_ HheadEmbed]].
  destruct (In_nth_error whole seg Hseg) as [i Hi].
  destruct HqHead as [t [Ht Htq]].
  destruct (Rlt_dec t 0) as [HtStrict | HtBody].
  - (* q は先頭 strict 延長上にある。 *)
    destruct i as [|i].
    + rewrite HheadNth in Hi. injection Hi as HsegHead. subst seg.
      destruct Hq as [Hq | Hq]; rewrite Hq in Htq.
      * assert (Ht0eq : t = 0).
        { apply (point_injective (hd_segment whole) t 0). exact Htq. }
        lra.
      * assert (Ht1 : t = 1).
        { apply (point_injective (hd_segment whole) t 1). exact Htq. }
        lra.
    + destruct (@nth_error_split Segment whole (S i) seg Hi)
        as [before [after [Hsplit Hlen]]].
      destruct (context_sparse l sub r Hctx before seg after Hsplit)
        as [Hext _].
      apply (Hext q).
      * left. split.
        -- intros Hnil. subst before. simpl in Hlen. lia.
        -- unfold onHead_extend_strict. exists t.
           split; [exact HtStrict |].
           change (point (hd_segment (before ++ seg :: after)) t = q).
           rewrite <- Hsplit. exact Htq.
      * destruct Hq as [-> | ->];
          apply segment_in_rect_or_endpoints; [apply onInit | apply onTerm].
  - (* q は先頭セグメント本体上にある。 *)
    assert (Ht0 : 0 <= t) by lra.
    assert (HqOnHead : onSegment (hd_segment whole) q).
    { exists t. split; [lra | exact Htq]. }
    destruct i as [|i].
    + rewrite HheadNth in Hi. injection Hi as HsegHead. subst seg.
      destruct v.
      * pose proof (embedded_head_trace_vertical_bound
                      (hd_segment whole) n h c above HheadEmbed Habove) as Htop.
        destruct Hq as [Hq | Hq].
        -- destruct Hp as [Hp | Hp].
           ++ rewrite Hp in Hbelowp. rewrite Hq in Hbelowq. lra.
           ++ pose proof (n_end_relation (hd_segment whole) h c HheadEmbed).
              rewrite Hp in Hbelowp. rewrite Hq in Hbelowq. lra.
        -- rewrite Hq in Hqabove. lra.
      * pose proof (embedded_head_trace_vertical_bound
                      (hd_segment whole) s h c below HheadEmbed Hbelow) as Hbottom.
        destruct Hq as [Hq | Hq].
        -- destruct Hp as [Hp | Hp].
           ++ rewrite Hp in Hbelowp. rewrite Hq in Hbelowq. lra.
           ++ assert (HbelowTerm : below = term (hd_segment whole)).
              { apply (south_head_trace_at_term_y
                         (hd_segment whole) h c below HheadEmbed Hbelow).
                now rewrite Hbelowp, Hp. }
              rewrite Hp in Hpx. apply Hpx. now rewrite HbelowTerm.
        -- rewrite Hq in Hbelowq. lra.
    + destruct Hq as [HqInit | HqTerm].
      * destruct i as [|i].
        -- (* q は先頭と直後のセグメントとの共有端点。 *)
           destruct (embed_scurve_adjacent_data
                       sc whole 0 (hd_segment whole) seg
                       Hembed HheadNth Hi)
             as [psHead [psSeg [HembHead [HembSeg [Hdc Hjoin]]]]].
           assert (HqTermHead : q = term (hd_segment whole)).
           { eapply adjacent_not_intersect_except_junction; eauto.
             rewrite HqInit. apply onInit. }
           destruct v.
           ++ pose proof (embedded_head_trace_vertical_bound
                            (hd_segment whole) n h c above
                            HheadEmbed Habove) as Htop.
              rewrite HqTermHead in Hqabove. lra.
           ++ pose proof (embedded_head_trace_vertical_bound
                            (hd_segment whole) s h c below
                            HheadEmbed Hbelow) as Hbottom.
              rewrite HqTermHead in Hbelowq. lra.
        -- (* 二つ以上離れた始点との接触は sparse 性に反する。 *)
           destruct (nth_error_far_in_nonadjacent_sides
                       whole (S (S i)) 0 seg (hd_segment whole)
                       Hi HheadNth ltac:(right; lia))
             as [before [after [Hsplit HinHead]]].
           destruct (context_sparse l sub r Hctx before seg after Hsplit)
             as [_ Hrect].
           apply (Hrect (hd_segment whole) q HinHead).
           ++ now apply segment_in_rect_or_endpoints.
           ++ rewrite HqInit. apply segment_in_rect_or_endpoints, onInit.
      * (* 後続セグメントの終点が先頭本体へ戻ることはない。 *)
        eapply (later_body_point_not_on_earlier_segment
                  sc whole 0 (S i) (hd_segment whole) seg 1
                  Hembed (context_sparse l sub r Hctx)
                  HheadNth Hi ltac:(lia) ltac:(lra)).
        replace (point seg 1) with q.
        -- exact HqOnHead.
Qed.

(* 埋め込まれた末尾 trace は、始点より垂直方向へ戻らない。 *)
Lemma embedded_last_trace_vertical_bound : forall seg v h c p,
  embed (v, h, c) seg ->
  onLastSegment seg p ->
  match v with
  | n => snd (init seg) <= snd p
  | s => snd p <= snd (init seg)
  end.
Proof.
  intros seg v h c [x y] Hembed [t [Ht <-]].
  destruct (Rle_dec t 1) as [Ht1 | Ht1].
  - assert (Hon : onSegment seg (point seg t)).
    { exists t. split; [lra | reflexivity]. }
    destruct v.
    + assert (Hon' : onSegment seg
        (fst (point seg t), snd (point seg t))).
      { replace (fst (point seg t), snd (point seg t)) with (point seg t)
          by apply surjective_pairing. exact Hon. }
      exact (proj1 (n_onseg_relation seg h c
                      (fst (point seg t)) (snd (point seg t)) Hembed Hon')).
    + assert (Hon' : onSegment seg
        (fst (point seg t), snd (point seg t))).
      { replace (fst (point seg t), snd (point seg t)) with (point seg t)
          by apply surjective_pairing. exact Hon. }
      exact (proj2 (s_onseg_relation seg h c
                      (fst (point seg t)) (snd (point seg t)) Hembed Hon')).
  - assert (Hlast : onLast seg (point seg t)).
    { exists t. split; [lra | reflexivity]. }
    destruct v.
    + pose proof (north_last_extension_bounds seg h c (point seg t)
                    Hembed Hlast) as Hext.
      pose proof (n_end_relation seg h c Hembed) as Hend. lra.
    + pose proof (south_last_extension_bounds seg h c (point seg t)
                    Hembed Hlast) as Hext.
      pose proof (s_end_relation seg h c Hembed) as Hend. lra.
Qed.

Lemma embedded_last_trace_horizontal_bound : forall seg v h c p,
  embed (v, h, c) seg ->
  onLastSegment seg p ->
  match h with
  | e => fst (init seg) <= fst p
  | w => fst p <= fst (init seg)
  end.
Proof.
  intros seg v h c [x y] Hembed [t [Ht <-]].
  destruct (Rle_dec t 1) as [Ht1 | Ht1].
  - assert (Hon : onSegment seg (point seg t)).
    { exists t. split; [lra | reflexivity]. }
    destruct h.
    + assert (Hon' : onSegment seg
          (fst (point seg t), snd (point seg t))).
      { replace (fst (point seg t), snd (point seg t)) with (point seg t)
          by apply surjective_pairing. exact Hon. }
      exact (proj1 (e_onseg_relation seg v c
                      (fst (point seg t)) (snd (point seg t)) Hembed Hon')).
    + assert (Hon' : onSegment seg
          (fst (point seg t), snd (point seg t))).
      { replace (fst (point seg t), snd (point seg t)) with (point seg t)
          by apply surjective_pairing. exact Hon. }
      exact (proj2 (w_onseg_relation seg v c
                      (fst (point seg t)) (snd (point seg t)) Hembed Hon')).
  - assert (Hlast : onLast seg (point seg t)).
    { exists t. split; [lra | reflexivity]. }
    destruct h.
    + pose proof (east_last_extension_bounds seg v c (point seg t)
                    Hembed Hlast).
      pose proof (e_end_relation seg v c Hembed). lra.
    + pose proof (west_last_extension_bounds seg v c (point seg t)
                    Hembed Hlast).
      pose proof (w_end_relation seg v c Hembed). lra.
Qed.

Lemma on_segment_init_from_y : forall seg p,
  onSegment seg p -> snd p = snd (init seg) -> p = init seg.
Proof.
  intros seg p [t [[Ht0 Ht1] <-]] Hy.
  assert (Ht : t = 0).
  { destruct (Req_dec t 0) as [-> | Hneq]; [reflexivity |].
    assert (Hlt : 0 < t) by lra.
    destruct (y_strictly_monotone_seg seg) as [Hinc | Hdec].
    - pose proof (Hinc 0 t ltac:(lra)) as Hstrict.
      unfold init in Hy. lra.
    - pose proof (Hdec 0 t ltac:(lra)) as Hstrict.
      unfold init in Hy. lra. }
  subst t. reflexivity.
Qed.

(* 北向き末尾 trace で始点と同じ高さを取る点は始点自身だけである。 *)
Lemma north_last_trace_at_init_y : forall seg h c p,
  embed (n, h, c) seg ->
  onLastSegment seg p ->
  snd p = snd (init seg) ->
  p = init seg.
Proof.
  intros seg h c [x y] Hembed [t [Ht Hpoint]] Hy.
  cbn in Hy. subst y.
  destruct (Rle_dec t 1) as [Ht1 | Ht1].
  - apply on_segment_init_from_y.
    exists t. split; [lra | exact Hpoint].
    reflexivity.
  - assert (Hlast : onLast seg (x, snd (init seg))).
    { exists t. split; [lra | exact Hpoint]. }
    pose proof (north_last_extension_bounds seg h c
                  (x, snd (init seg)) Hembed Hlast) as Hext.
    pose proof (n_end_relation seg h c Hembed) as Hend. cbn in Hext. lra.
Qed.

(* [later_body_point_not_on_earlier_segment] の双対。前のセグメントの
   終点を除く本体点は、後のセグメント上へ戻らない。 *)
Lemma earlier_body_point_not_on_later_segment :
  forall sc ls earlier later s_earlier s_later u,
    embed_scurve sc ls ->
    sparse_embedding ls ->
    nth_error ls earlier = Some s_earlier ->
    nth_error ls later = Some s_later ->
    (earlier < later)%nat ->
    0 <= u < 1 ->
    onSegment s_later (point s_earlier u) ->
    False.
Proof.
  intros sc ls earlier later s_earlier s_later u
    Hembed Hsparse Hearlier Hlater Hlt Hu HonLater.
  assert (HonEarlier : onSegment s_earlier (point s_earlier u)).
  { exists u. split; [split; lra | reflexivity]. }
  destruct (Nat.eq_dec later (S earlier)) as [Hadj | Hfar].
  - subst later.
    destruct (embed_scurve_adjacent_data
                sc ls earlier s_earlier s_later
                Hembed Hearlier Hlater)
      as [ps1 [ps2 [Hembed1 [Hembed2 [Hdc Hjoin]]]]].
    pose proof (adjacent_not_intersect_except_junction
                  ps1 ps2 s_earlier s_later (point s_earlier u)
                  Hdc Hembed1 Hembed2 Hjoin HonEarlier HonLater) as Hp.
    assert (Hone : u = 1).
    { apply (point_injective s_earlier u 1).
      change (point s_earlier u = term s_earlier). exact Hp. }
    lra.
  - assert (Hfar' : (S earlier < later)%nat) by lia.
    destruct (nth_error_far_in_nonadjacent_sides
                ls earlier later s_earlier s_later
                Hearlier Hlater ltac:(left; exact Hfar'))
      as [before [after [Hsplit HinLater]]].
    destruct (Hsparse before s_earlier after Hsplit) as [_ Hrect].
    apply (Hrect s_later (point s_earlier u) HinLater).
    + now apply segment_in_rect_or_endpoints.
    + now apply segment_in_rect_or_endpoints.
Qed.

(* 末尾 trace についての双対。末尾以前の各出現との位置関係だけが
   異なり、衝突を排除する三つの理由は先頭の場合と同じである。 *)
Lemma last_trace_cannot_straddle_segment_endpoint :
  forall l sub r seg p q below above,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    onLastSegment (last_segment (l ++ sub ++ r)) below ->
    onLastSegment (last_segment (l ++ sub ++ r)) q ->
    onLastSegment (last_segment (l ++ sub ++ r)) above ->
    snd below = snd p ->
    fst p <> fst below ->
    snd below < snd q ->
    snd q < snd above ->
    False.
Proof.
  intros l sub r seg p q below above Hctx Hseg Hp Hq
    Hbelow HqLast Habove Hbelowp Hpx Hbelowq Hqabove.
  set (whole := l ++ sub ++ r) in *.
  assert (Hwhole : whole <> []).
  { unfold whole. now apply whole_nonempty, context_sub_nonempty
      with (l := l) (r := r). }
  set (last_i := (length whole - 1)%nat).
  assert (HlastNth : nth_error whole last_i = Some (last_segment whole)).
  { unfold last_i. now apply nth_error_last. }
  destruct (context_whole_embedded l sub r Hctx)
    as [ds [sc [_ Hembed]]].
  change (embed_scurve sc whole) in Hembed.
  destruct (embed_scurve_nth_embed sc whole Hembed last_i
              (last_segment whole) HlastNth)
    as [[[v h] c] [_ HlastEmbed]].
  destruct (In_nth_error whole seg Hseg) as [i Hi].
  assert (HiBound : (i <= last_i)%nat).
  { apply nth_error_lt in Hi. unfold last_i. lia. }
  destruct HqLast as [t [Ht Htq]].
  destruct (Rlt_dec 1 t) as [HtStrict | HtBody].
  - (* q は末尾 strict 延長上にある。 *)
    destruct (Nat.eq_dec i last_i) as [Heq | Hneq].
    + subst i. rewrite HlastNth in Hi. injection Hi as HsegLast. subst seg.
      destruct Hq as [Hq | Hq]; rewrite Hq in Htq.
      * assert (Ht0eq : t = 0).
        { apply (point_injective (last_segment whole) t 0). exact Htq. }
        lra.
      * assert (Ht1eq : t = 1).
        { apply (point_injective (last_segment whole) t 1). exact Htq. }
        lra.
    + assert (HiLt : (i < last_i)%nat) by lia.
      destruct (@nth_error_split Segment whole i seg Hi)
        as [before [after [Hsplit Hlen]]].
      destruct (context_sparse l sub r Hctx before seg after Hsplit)
        as [Hext _].
      apply (Hext q).
      * right. split.
        -- intros Hnil. subst after.
           pose proof (f_equal (@length Segment) Hsplit) as Hlength.
           unfold last_i in HiLt. rewrite length_app in Hlength.
           simpl in Hlength. lia.
        -- unfold onLast_extend_strict. exists t.
           split; [exact HtStrict |].
           change (point (last_segment (before ++ seg :: after)) t = q).
           rewrite <- Hsplit. exact Htq.
      * destruct Hq as [-> | ->];
          apply segment_in_rect_or_endpoints; [apply onInit | apply onTerm].
  - (* q は末尾セグメント本体上にある。 *)
    assert (Ht1 : t <= 1) by lra.
    assert (HqOnLast : onSegment (last_segment whole) q).
    { exists t. split; [lra | exact Htq]. }
    destruct (Nat.eq_dec i last_i) as [Heq | Hneq].
    + subst i. rewrite HlastNth in Hi. injection Hi as HsegLast. subst seg.
      destruct v.
      * pose proof (embedded_last_trace_vertical_bound
                      (last_segment whole) n h c below HlastEmbed Hbelow)
          as Hbottom.
        destruct Hq as [Hq | Hq].
        -- rewrite Hq in Hbelowq. lra.
        -- destruct Hp as [Hp | Hp].
           ++ assert (HbelowInit : below = init (last_segment whole)).
              { apply (north_last_trace_at_init_y
                         (last_segment whole) h c below HlastEmbed Hbelow).
                now rewrite Hbelowp, Hp. }
              rewrite Hp in Hpx. apply Hpx. now rewrite HbelowInit.
           ++ rewrite Hp in Hbelowp. rewrite Hq in Hbelowq. lra.
      * pose proof (embedded_last_trace_vertical_bound
                      (last_segment whole) s h c above HlastEmbed Habove)
          as Htop.
        destruct Hq as [Hq | Hq].
        -- rewrite Hq in Hqabove. lra.
        -- destruct Hp as [Hp | Hp].
           ++ pose proof (s_end_relation (last_segment whole) h c HlastEmbed).
              rewrite Hp in Hbelowp. rewrite Hq in Hbelowq. lra.
           ++ rewrite Hp in Hbelowp. rewrite Hq in Hbelowq. lra.
    + assert (HiLt : (i < last_i)%nat) by lia.
      destruct Hq as [HqInit | HqTerm].
      * (* 以前のセグメントの始点が末尾本体へ戻ることはない。 *)
        eapply (earlier_body_point_not_on_later_segment
                  sc whole i last_i seg (last_segment whole) 0
                  Hembed (context_sparse l sub r Hctx)
                  Hi HlastNth HiLt ltac:(lra)).
        replace (point seg 0) with q.
        -- exact HqOnLast.
      * destruct (Nat.eq_dec last_i (S i)) as [Hadj | Hfar].
        -- (* q は直前と末尾セグメントとの共有端点。 *)
           destruct (embed_scurve_adjacent_data
                       sc whole i seg (last_segment whole)
                       Hembed Hi ltac:(now rewrite <- Hadj))
             as [psSeg [psLast [HembSeg [HembLast [Hdc Hjoin]]]]].
           assert (HqInitLast : q = init (last_segment whole)).
           { rewrite <- Hjoin.
             eapply adjacent_not_intersect_except_junction; eauto.
             rewrite HqTerm. apply onTerm. }
           destruct v.
           ++ pose proof (embedded_last_trace_vertical_bound
                            (last_segment whole) n h c below
                            HlastEmbed Hbelow) as Hbottom.
              rewrite HqInitLast in Hbelowq. lra.
           ++ pose proof (embedded_last_trace_vertical_bound
                            (last_segment whole) s h c above
                            HlastEmbed Habove) as Htop.
              rewrite HqInitLast in Hqabove. lra.
        -- (* 二つ以上離れた終点との接触は sparse 性に反する。 *)
           assert (Hfar' : (S i < last_i)%nat) by lia.
           destruct (nth_error_far_in_nonadjacent_sides
                       whole i last_i seg (last_segment whole)
                       Hi HlastNth ltac:(left; exact Hfar'))
             as [before [after [Hsplit HinLast]]].
           destruct (context_sparse l sub r Hctx before seg after Hsplit)
             as [_ Hrect].
           apply (Hrect (last_segment whole) q HinLast).
           ++ now apply segment_in_rect_or_endpoints.
           ++ rewrite HqTerm. apply segment_in_rect_or_endpoints, onTerm.
Qed.

(* 端点 q の上下に実在する右上がりの end trace が q に触れる場合を、
   上の先頭・末尾二ケースへ還元する。 *)
Lemma two_sided_rising_barrier_endpoint_contact_impossible :
  forall l sub r seg p q side below above,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    (l ++ sub ++ r) <> [] ->
    right_rising_barrier side (l ++ sub ++ r) ->
    on_barrier_trace side (l ++ sub ++ r) below ->
    on_barrier_trace side (l ++ sub ++ r) q ->
    on_barrier_trace side (l ++ sub ++ r) above ->
    snd below = snd p ->
    fst p < fst below ->
    snd below < snd q ->
    snd q < snd above ->
    False.
Proof.
  intros l sub r seg p q side below above Hctx Hseg Hp Hq
    Hwhole Hrising Hbelow Hqbar Habove Hbp Hpx Hbelowq Hqabove.
  destruct side; cbn in *.
  - apply (head_trace_cannot_straddle_segment_endpoint
             l sub r seg p q below above Hctx Hseg Hp Hq
             Hbelow Hqbar Habove Hbp); lra.
  - apply (last_trace_cannot_straddle_segment_endpoint
             l sub r seg p q below above Hctx Hseg Hp Hq
             Hbelow Hqbar Habove Hbp); lra.
Qed.

(* 右下がりの場合も、x の不等号の向きだけを変えて同じ二ケースへ
   還元できる。 *)
Lemma two_sided_falling_barrier_endpoint_contact_impossible :
  forall l sub r seg p q side below above,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    (l ++ sub ++ r) <> [] ->
    right_falling_barrier side (l ++ sub ++ r) ->
    on_barrier_trace side (l ++ sub ++ r) below ->
    on_barrier_trace side (l ++ sub ++ r) q ->
    on_barrier_trace side (l ++ sub ++ r) above ->
    snd below = snd p ->
    fst below < fst p ->
    snd below < snd q ->
    snd q < snd above ->
    False.
Proof.
  intros l sub r seg p q side below above Hctx Hseg Hp Hq
    Hwhole Hfalling Hbelow Hqbar Habove Hbp Hpx Hbelowq Hqabove.
  destruct side; cbn in *.
  - apply (head_trace_cannot_straddle_segment_endpoint
             l sub r seg p q below above Hctx Hseg Hp Hq
             Hbelow Hqbar Habove Hbp); lra.
  - apply (last_trace_cannot_straddle_segment_endpoint
             l sub r seg p q below above Hctx Hseg Hp Hq
             Hbelow Hqbar Habove Hbp); lra.
Qed.

(* strict 障壁は q の下から anchor の高さまで続く。従って、
   p から同一セグメントを上がった q が障壁の端点に接触すると、
   非隣接交差または隣接端点の単調性に反する。 *)
Lemma same_segment_left_strict_guard_contact_impossible :
  forall l sub r seg p q,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    snd p <= snd q ->
    fst q < fst (sub_left_anchor sub) ->
    snd q < snd (sub_left_anchor sub) ->
    left_strict_guard_contact l sub r p q ->
    False.
Proof.
  intros l sub r seg [xp yp] [xq yq] Hctx Hseg Hp Hq Hy Hqx Hqy.
  unfold left_strict_guard_contact. cbn.
  intros [side [HbarWhole [Hrising [HpTop [Hspan Hcontact]]]]].
  destruct (Hspan yp ltac:(lra)) as [xb [[Hpxb _] Hbelow]].
  destruct (Hspan (snd (sub_left_anchor sub)) ltac:(lra))
    as [xt [_ Habove]].
  assert (Hpq : (xp, yp) <> (xq, yq)).
  { intros Heq. injection Heq as Hxeq Hyeq. subst xq yq.
    pose proof (right_rising_barrier_same_height_unique
                  side (l ++ sub ++ r) (xb, yp) (xp, yp)
                  Hrising Hbelow Hcontact eq_refl) as Hequal.
    pose proof (f_equal fst Hequal) as Hx. cbn in Hx. lra. }
  assert (Hylt : yp < yq).
  { destruct Hp as [Hp | Hp], Hq as [Hq | Hq].
    - exfalso. apply Hpq. now rewrite Hp, Hq.
    - pose proof (f_equal snd Hp) as Hpy.
      pose proof (f_equal snd Hq) as Hqy'. cbn in Hpy, Hqy'.
      destruct (Rle_lt_or_eq_dec yp yq Hy) as [Hlt | Heq]; [exact Hlt |].
      exfalso. apply (neq_init_term_y seg). unfold init_y, term_y.
      rewrite <- Hpy, <- Hqy'. exact Heq.
    - pose proof (f_equal snd Hp) as Hpy.
      pose proof (f_equal snd Hq) as Hqy'. cbn in Hpy, Hqy'.
      destruct (Rle_lt_or_eq_dec yp yq Hy) as [Hlt | Heq]; [exact Hlt |].
      exfalso. apply (neq_init_term_y seg). unfold init_y, term_y.
      rewrite <- Hqy', <- Hpy. exact (eq_sym Heq).
    - exfalso. apply Hpq. now rewrite Hp, Hq. }
  eapply two_sided_rising_barrier_endpoint_contact_impossible
    with (seg := seg) (p := (xp, yp)) (side := side)
         (below := (xb, yp)) (above := (xt, snd (sub_left_anchor sub)));
    eauto; cbn; lra.
Qed.

Lemma same_segment_right_strict_guard_contact_impossible :
  forall l sub r seg p q,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    snd p <= snd q ->
    fst (sub_right_anchor sub) < fst q ->
    snd q < snd (sub_right_anchor sub) ->
    right_strict_guard_contact l sub r p q ->
    False.
Proof.
  intros l sub r seg [xp yp] [xq yq] Hctx Hseg Hp Hq Hy Hqx Hqy.
  unfold right_strict_guard_contact. cbn.
  intros [side [HbarWhole [Hfalling [HpTop [Hspan Hcontact]]]]].
  destruct (Hspan yp ltac:(lra)) as [xb [[_ Hxbp] Hbelow]].
  destruct (Hspan (snd (sub_right_anchor sub)) ltac:(lra))
    as [xt [_ Habove]].
  assert (Hpq : (xp, yp) <> (xq, yq)).
  { intros Heq. injection Heq as Hxeq Hyeq. subst xq yq.
    pose proof (right_falling_barrier_same_height_unique
                  side (l ++ sub ++ r) (xb, yp) (xp, yp)
                  Hfalling Hbelow Hcontact eq_refl) as Hequal.
    pose proof (f_equal fst Hequal) as Hx. cbn in Hx. lra. }
  assert (Hylt : yp < yq).
  { destruct Hp as [Hp | Hp], Hq as [Hq | Hq].
    - exfalso. apply Hpq. now rewrite Hp, Hq.
    - pose proof (f_equal snd Hp) as Hpy.
      pose proof (f_equal snd Hq) as Hqy'. cbn in Hpy, Hqy'.
      destruct (Rle_lt_or_eq_dec yp yq Hy) as [Hlt | Heq]; [exact Hlt |].
      exfalso. apply (neq_init_term_y seg). unfold init_y, term_y.
      rewrite <- Hpy, <- Hqy'. exact Heq.
    - pose proof (f_equal snd Hp) as Hpy.
      pose proof (f_equal snd Hq) as Hqy'. cbn in Hpy, Hqy'.
      destruct (Rle_lt_or_eq_dec yp yq Hy) as [Hlt | Heq]; [exact Hlt |].
      exfalso. apply (neq_init_term_y seg). unfold init_y, term_y.
      rewrite <- Hqy', <- Hpy. exact (eq_sym Heq).
    - exfalso. apply Hpq. now rewrite Hp, Hq. }
  eapply two_sided_falling_barrier_endpoint_contact_impossible
    with (seg := seg) (p := (xp, yp)) (side := side)
         (below := (xb, yp)) (above := (xt, snd (sub_right_anchor sub)));
    eauto; cbn; lra.
Qed.

(* 例外端点の役割は、そこから sub 以下の危険点へ直接出る
   order step を拒むことに限られる。 *)
Lemma barrier_exception_locally_blocks_unsafe_up : forall l sub r p,
  ClassificationContext l sub r ->
  barrier_exception l sub r p ->
  locally_blocks_unsafe_up l sub r p.
Admitted.

(* 同一セグメントの通常辺について、直接の障壁を左下領域の
   不変量証明書へ移す。右へ抜ければ交差、等号接触も上の補題に反する。 *)
Lemma same_segment_upward_preserves_direct_left_certificate :
  forall l sub r seg p q,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    snd p <= snd q ->
    left_vertical_guard_to_init l sub r p ->
    fst q < fst (sub_left_anchor sub) ->
    snd q < snd (sub_left_anchor sub) ->
    left_up_certificate l sub r q.
Proof.
  intros l sub r seg p q Hctx Hseg Hp Hq Hy Hguard Hqx Hqy.
  destruct (left_guard_preserved_by_same_segment_or_contact
              l sub r seg p q Hctx Hseg Hp Hq Hy Hguard Hqx Hqy)
      as [Hguard' | Hcontact].
    - destruct Hguard' as [side [Hcore Hlevel]].
      exact (left_certificate_at_level l sub r side q Hcore Hlevel).
  - exfalso.
    exact (same_segment_left_strict_guard_contact_impossible
             l sub r seg p q Hctx Hseg Hp Hq Hy Hqx Hqy Hcontact).
Qed.

Lemma same_segment_upward_preserves_direct_right_certificate :
  forall l sub r seg p q,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    snd p <= snd q ->
    right_vertical_guard_to_term l sub r p ->
    fst (sub_right_anchor sub) < fst q ->
    snd q < snd (sub_right_anchor sub) ->
    right_up_certificate l sub r q.
Proof.
  intros l sub r seg p q Hctx Hseg Hp Hq Hy Hguard Hqx Hqy.
  destruct (right_guard_preserved_by_same_segment_or_contact
              l sub r seg p q Hctx Hseg Hp Hq Hy Hguard Hqx Hqy)
      as [Hguard' | Hcontact].
    - destruct Hguard' as [side [Hcore Hlevel]].
      exact (right_certificate_at_level l sub r side q Hcore Hlevel).
  - exfalso.
    exact (same_segment_right_strict_guard_contact_impossible
             l sub r seg p q Hctx Hseg Hp Hq Hy Hqx Hqy Hcontact).
Qed.

Lemma up_path_invariant_not_on_sub : forall l sub r p,
  ClassificationContext l sub r ->
  up_path_invariant l sub r p ->
  ~ onSegmentlist sub p.
Proof.
  intros l sub r p Hctx [Hcenter _] Hsub.
  apply (strictly_above_sub_at_x_not_on_sub sub p
           (Hcenter
             (x_monotone_sub_point_in_x_range sub p
               (context_sub_nonempty l sub r Hctx)
               (context_sub_connected l sub r Hctx)
               (context_sub_x_monotone l sub r Hctx) Hsub))).
  exact Hsub.
Qed.

(* ----------------------------------------------------------------- *)
(*  Up 不変量を一つの順序辺に沿って移すための幾何学的補題       *)
(* ----------------------------------------------------------------- *)

(* 同一セグメントが sub の x 範囲へ入る場合、sub との上下関係は
   交差なしに反転しない。連続性の中間値部分は後で幾何補題へ切り出す。 *)
Lemma same_segment_upward_preserves_sub_above :
  forall l sub r seg p q,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    snd p <= snd q ->
    up_path_invariant l sub r p ->
    in_sub_x_range sub q ->
    strictly_above_sub_at_x sub q.
Admitted.

(* 例外下端から上向きに進む場合。同じ side の open core と、下端が
   その trace 自身に属するという destruct 済みの証明書を受け取る。 *)
Lemma ordered_distinct_segment_endpoints_strict_y :
  forall seg p q,
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    p <> q ->
    snd p <= snd q ->
    snd p < snd q.
Proof.
  intros seg p q Hp Hq Hneq Hle.
  destruct (Rle_lt_or_eq_dec (snd p) (snd q) Hle) as [Hlt | Heq];
    [exact Hlt |].
  destruct Hp as [Hp | Hp], Hq as [Hq | Hq].
  - exfalso. apply Hneq. now rewrite Hp, Hq.
  - exfalso. apply (neq_init_term_y seg). unfold init_y, term_y.
    rewrite <- (f_equal snd Hp), <- (f_equal snd Hq). exact Heq.
  - exfalso. apply (neq_init_term_y seg). unfold init_y, term_y.
    rewrite <- (f_equal snd Hq), <- (f_equal snd Hp). exact (eq_sym Heq).
  - exfalso. apply Hneq. now rewrite Hp, Hq.
Qed.

Lemma dc_after_rising_head_moves_left :
  forall ps_bar ps_seg bar seg above,
    dc ps_bar ps_seg ->
    embed ps_bar bar ->
    embed ps_seg seg ->
    snd (init seg) < snd (term seg) ->
    onHeadSegment bar above ->
    snd (term bar) < snd above ->
    fst (term bar) < fst above ->
    fst (term seg) < fst (init seg).
Proof.
  intros ps_bar ps_seg bar seg above Hdc Hbar Hseg HsegY Habove HaboveY HaboveX.
  destruct Hdc as [v h c | h | h | h | h].
  - destruct v.
    + pose proof (embedded_head_trace_vertical_bound bar n h c above Hbar Habove).
      lra.
    + pose proof (s_end_relation seg h (i_c c) Hseg). lra.
  - pose proof (s_end_relation seg h cx Hseg). lra.
  - destruct h.
    + pose proof (embedded_head_trace_horizontal_bound bar s e cc above Hbar Habove).
      lra.
    + exact (w_end_relation seg n cc Hseg).
  - pose proof (embedded_head_trace_vertical_bound bar n h cc above Hbar Habove).
    lra.
  - pose proof (s_end_relation seg (i_h h) cc Hseg). lra.
Qed.

Lemma dc_before_rising_last_moves_left :
  forall ps_seg ps_bar seg bar above,
    dc ps_seg ps_bar ->
    embed ps_seg seg ->
    embed ps_bar bar ->
    snd (term seg) < snd (init seg) ->
    onLastSegment bar above ->
    snd (init bar) < snd above ->
    fst (init bar) < fst above ->
    fst (init seg) < fst (term seg).
Proof.
  intros ps_seg ps_bar seg bar above Hdc Hseg Hbar HsegY Habove HaboveY HaboveX.
  destruct Hdc as [v h c | h | h | h | h].
  - destruct v.
    + pose proof (n_end_relation seg h c Hseg). lra.
    + pose proof (embedded_last_trace_vertical_bound bar s h (i_c c)
                    above Hbar Habove). lra.
  - pose proof (n_end_relation seg h cx Hseg). lra.
  - destruct h.
    + exact (e_end_relation seg s cc Hseg).
    + pose proof (embedded_last_trace_horizontal_bound bar n w cc
                    above Hbar Habove). lra.
  - pose proof (n_end_relation seg h cc Hseg). lra.
  - pose proof (embedded_last_trace_vertical_bound bar s (i_h h) cc
                  above Hbar Habove). lra.
Qed.

Lemma dc_after_falling_head_moves_right :
  forall ps_bar ps_seg bar seg above,
    dc ps_bar ps_seg ->
    embed ps_bar bar ->
    embed ps_seg seg ->
    snd (init seg) < snd (term seg) ->
    onHeadSegment bar above ->
    snd (term bar) < snd above ->
    fst above < fst (term bar) ->
    fst (init seg) < fst (term seg).
Proof.
  intros ps_bar ps_seg bar seg above Hdc Hbar Hseg HsegY Habove HaboveY HaboveX.
  destruct Hdc as [v h c | h | h | h | h].
  - destruct v.
    + pose proof (embedded_head_trace_vertical_bound bar n h c above Hbar Habove).
      lra.
    + pose proof (s_end_relation seg h (i_c c) Hseg). lra.
  - pose proof (s_end_relation seg h cx Hseg). lra.
  - destruct h.
    + exact (e_end_relation seg n cc Hseg).
    + pose proof (embedded_head_trace_horizontal_bound bar s w cc above Hbar Habove).
      lra.
  - pose proof (embedded_head_trace_vertical_bound bar n h cc above Hbar Habove).
    lra.
  - pose proof (s_end_relation seg (i_h h) cc Hseg). lra.
Qed.

Lemma dc_before_falling_last_moves_right :
  forall ps_seg ps_bar seg bar above,
    dc ps_seg ps_bar ->
    embed ps_seg seg ->
    embed ps_bar bar ->
    snd (term seg) < snd (init seg) ->
    onLastSegment bar above ->
    snd (init bar) < snd above ->
    fst above < fst (init bar) ->
    fst (term seg) < fst (init seg).
Proof.
  intros ps_seg ps_bar seg bar above Hdc Hseg Hbar HsegY Habove HaboveY HaboveX.
  destruct Hdc as [v h c | h | h | h | h].
  - destruct v.
    + pose proof (n_end_relation seg h c Hseg). lra.
    + pose proof (embedded_last_trace_vertical_bound bar s h (i_c c)
                    above Hbar Habove). lra.
  - pose proof (n_end_relation seg h cx Hseg). lra.
  - destruct h.
    + pose proof (embedded_last_trace_horizontal_bound bar n e cc
                    above Hbar Habove). lra.
    + exact (w_end_relation seg s cc Hseg).
  - pose proof (n_end_relation seg h cc Hseg). lra.
  - pose proof (embedded_last_trace_vertical_bound bar s (i_h h) cc
                  above Hbar Habove). lra.
Qed.

(* 障壁とは異なるセグメントがその下端に接続する場合、非隣接なら sparse、
   隣接なら dc により、上側端点は左外向きにしか進めない。 *)
Lemma distinct_segment_from_rising_barrier_moves_left :
  forall l sub r seg p q side,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    p <> q ->
    snd p <= snd q ->
    right_rising_barrier side (l ++ sub ++ r) ->
    on_barrier_trace side (l ++ sub ++ r) p ->
    (exists above,
        on_barrier_trace side (l ++ sub ++ r) above
        /\ snd p < snd above
        /\ fst p < fst above) ->
    seg <> barrier_segment side (l ++ sub ++ r) ->
    fst q < fst p.
Proof.
  intros l sub r seg p q side Hctx Hseg Hp Hq Hneq Hy Hrising Htrace
    [above [Habove [Hpy Hpx]]] Hne.
  assert (Hylt : snd p < snd q).
  { exact (ordered_distinct_segment_endpoints_strict_y seg p q Hp Hq Hneq Hy). }
  set (whole := l ++ sub ++ r) in *.
  assert (Hwhole : whole <> []).
  { unfold whole. now apply whole_nonempty, context_sub_nonempty
      with (l := l) (r := r). }
  destruct (context_whole_embedded l sub r Hctx) as [ds [sc [_ Hembed]]].
  change (embed_scurve sc whole) in Hembed.
  destruct side.
  - cbn in Htrace, Habove, Hne, Hrising.
    assert (HheadNth : nth_error whole 0 = Some (hd_segment whole)).
    { destruct whole as [|head tail]; [contradiction | reflexivity]. }
    destruct (embed_scurve_nth_embed sc whole Hembed 0
                (hd_segment whole) HheadNth)
      as [psHead [_ HembHead]].
    destruct (In_nth_error whole seg Hseg) as [i Hi].
    destruct Htrace as [t [Ht Htp]].
    destruct (Rlt_dec t 0) as [HtStrict | HtBody].
    + destruct (@nth_error_split Segment whole i seg Hi)
        as [before [after [Hsplit Hlen]]].
      destruct (context_sparse l sub r Hctx before seg after Hsplit)
        as [Hext _].
      exfalso.
      apply (Hext p).
      * left. split.
          -- intros Hnil. subst before. simpl in Hlen. subst i.
             rewrite HheadNth in Hi. injection Hi as Heq.
             apply Hne. exact (eq_sym Heq).
        -- unfold onHead_extend_strict. exists t. split; [exact HtStrict |].
           change (point (hd_segment (before ++ seg :: after)) t = p).
           rewrite <- Hsplit. exact Htp.
      * destruct Hp as [-> | ->];
          apply segment_in_rect_or_endpoints; [apply onInit | apply onTerm].
    + assert (HpHead : onSegment (hd_segment whole) p).
      { exists t. split; [lra | exact Htp]. }
      destruct i as [|i].
        * exfalso. apply Hne.
          rewrite HheadNth in Hi. now injection Hi as Heq.
      * destruct Hp as [HpInit | HpTerm].
        -- destruct i as [|i].
           ++ destruct (embed_scurve_adjacent_data
                         sc whole 0 (hd_segment whole) seg
                         Hembed HheadNth Hi)
                as [psSegHead [psSeg [HembHead' [HembSeg [Hdc Hjoin]]]]].
              assert (HpJoin : p = term (hd_segment whole)).
              { eapply adjacent_not_intersect_except_junction; eauto.
                rewrite HpInit. apply onInit. }
              destruct Hq as [HqInit | HqTerm].
              ** exfalso. apply Hneq. now rewrite HpInit, HqInit.
              ** pose proof (dc_after_rising_head_moves_left
                               psSegHead psSeg (hd_segment whole) seg above
                               Hdc HembHead' HembSeg ltac:(rewrite <- HpInit, <- HqTerm; exact Hylt)
                               Habove ltac:(rewrite <- HpJoin; exact Hpy)
                               ltac:(rewrite <- HpJoin; exact Hpx)) as Hleft.
                 now rewrite HpInit, HqTerm.
           ++ destruct (nth_error_far_in_nonadjacent_sides
                         whole (S (S i)) 0 seg (hd_segment whole)
                         Hi HheadNth ltac:(right; lia))
                as [before [after [Hsplit HinHead]]].
              destruct (context_sparse l sub r Hctx before seg after Hsplit)
                as [_ Hrect].
              exfalso.
              apply (Hrect (hd_segment whole) p HinHead).
              ** exact (segment_in_rect_or_endpoints _ _ HpHead).
              ** rewrite HpInit. apply segment_in_rect_or_endpoints, onInit.
        -- exfalso. eapply (later_body_point_not_on_earlier_segment
                     sc whole 0 (S i) (hd_segment whole) seg 1
                     Hembed (context_sparse l sub r Hctx)
                     HheadNth Hi ltac:(lia) ltac:(lra)).
             replace (point seg 1) with p by exact HpTerm.
           exact HpHead.
  - cbn in Htrace, Habove, Hne, Hrising.
    set (last_i := (length whole - 1)%nat).
    assert (HlastNth : nth_error whole last_i = Some (last_segment whole)).
    { unfold last_i. now apply nth_error_last. }
    destruct (embed_scurve_nth_embed sc whole Hembed last_i
                (last_segment whole) HlastNth)
      as [psLast [_ HembLast]].
    destruct (In_nth_error whole seg Hseg) as [i Hi].
    assert (HiBound : (i <= last_i)%nat).
    { apply nth_error_lt in Hi. unfold last_i. lia. }
    destruct Htrace as [t [Ht Htp]].
    destruct (Rlt_dec 1 t) as [HtStrict | HtBody].
    + destruct (@nth_error_split Segment whole i seg Hi)
        as [before [after [Hsplit Hlen]]].
      destruct (context_sparse l sub r Hctx before seg after Hsplit)
        as [Hext _].
      exfalso.
        apply (Hext p).
        * right. split.
          -- intros Hnil. subst after. apply Hne. rewrite Hsplit.
             rewrite last_app_nonnil by discriminate. reflexivity.
        -- unfold onLast_extend_strict. exists t. split; [exact HtStrict |].
           change (point (last_segment (before ++ seg :: after)) t = p).
           rewrite <- Hsplit. exact Htp.
      * destruct Hp as [-> | ->];
          apply segment_in_rect_or_endpoints; [apply onInit | apply onTerm].
    + assert (HpLast : onSegment (last_segment whole) p).
      { exists t. split; [lra | exact Htp]. }
      destruct (Nat.eq_dec i last_i) as [Heq | Hlt].
        * exfalso. apply Hne.
          subst i. rewrite HlastNth in Hi. now injection Hi as Hsame.
      * assert (HiLt : (i < last_i)%nat) by lia.
        destruct Hp as [HpInit | HpTerm].
        -- exfalso. eapply (earlier_body_point_not_on_later_segment
                     sc whole i last_i seg (last_segment whole) 0
                     Hembed (context_sparse l sub r Hctx)
                     Hi HlastNth HiLt ltac:(lra)).
             replace (point seg 0) with p by exact HpInit.
           exact HpLast.
        -- destruct (Nat.eq_dec last_i (S i)) as [Hadj | Hfar].
           ++ destruct (embed_scurve_adjacent_data
                         sc whole i seg (last_segment whole)
                         Hembed Hi ltac:(now rewrite <- Hadj))
                as [psSeg [psLast' [HembSeg [HembLast' [Hdc Hjoin]]]]].
              assert (HpJoin : p = init (last_segment whole)).
              { rewrite <- Hjoin. exact HpTerm. }
              destruct Hq as [HqInit | HqTerm].
              ** pose proof (dc_before_rising_last_moves_left
                               psSeg psLast' seg (last_segment whole) above
                               Hdc HembSeg HembLast'
                               ltac:(rewrite <- HpTerm, <- HqInit; exact Hylt)
                               Habove ltac:(rewrite <- HpJoin; exact Hpy)
                               ltac:(rewrite <- HpJoin; exact Hpx)) as Hleft.
                 now rewrite HpTerm, HqInit.
              ** exfalso. apply Hneq. now rewrite HpTerm, HqTerm.
           ++ assert (Hfar' : (S i < last_i)%nat) by lia.
              destruct (nth_error_far_in_nonadjacent_sides
                         whole i last_i seg (last_segment whole)
                         Hi HlastNth ltac:(left; exact Hfar'))
                as [before [after [Hsplit HinLast]]].
              destruct (context_sparse l sub r Hctx before seg after Hsplit)
                as [_ Hrect].
              exfalso.
              apply (Hrect (last_segment whole) p HinLast).
              ** exact (segment_in_rect_or_endpoints _ _ HpLast).
              ** rewrite HpTerm. apply segment_in_rect_or_endpoints, onTerm.
Qed.

Lemma same_segment_left_exception_moves_outward_or_is_barrier :
  forall l sub r seg p q side,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    p <> q ->
    snd p <= snd q ->
    left_barrier_core side l sub r p ->
    barrier_exception l sub r p ->
    on_barrier_trace side (l ++ sub ++ r) p ->
    fst q < fst (sub_left_anchor sub) ->
    snd q < snd (sub_left_anchor sub) ->
    fst q < fst p
    \/ seg = barrier_segment side (l ++ sub ++ r).
(* 障壁自身でなければ、先頭・末尾との隣接関係を場合分けし、内向きなら
   dc に反する。障壁自身の上を進む場合だけを右の選言へ分離する。 *)
Proof.
  intros l sub r seg p q side Hctx Hseg Hp Hq Hneq Hy Hcore
    Hexception Htrace Hqx Hqy.
  destruct (classic (seg = barrier_segment side (l ++ sub ++ r))) as [Heq | Hne].
  - now right.
  - left.
    pose proof Hcore as Hcore'.
    unfold left_barrier_core in Hcore'. cbn in Hcore'.
    destruct Hcore' as [Hwhole [Hrising [Hpx [Hpy Hopen]]]].
    destruct (Hopen (snd (sub_left_anchor sub)) ltac:(lra))
      as [x [[Hpxx Hxleft] Htracex]].
    apply (distinct_segment_from_rising_barrier_moves_left
             l sub r seg p q side Hctx Hseg Hp Hq Hneq Hy Hrising Htrace).
    + exists (x, snd (sub_left_anchor sub)). repeat split; try assumption; cbn; lra.
    + exact Hne.
Qed.

(* 延長線 seed の end trace は反対側端点で本体端に達するため、その端点
   より高い点を同じ trace 上に持たない。左右の core から共通して使う。 *)
Lemma extension_seed_barrier_trace_bounded_by_other_endpoint :
  forall l sub r seg p q above side,
    ClassificationContext l sub r ->
    endpoint_of_seg seg q ->
    p <> q ->
    snd p <= snd q ->
    barrier_extension_seed l sub r side p ->
    on_barrier_trace side (l ++ sub ++ r) above ->
    snd q < snd above ->
    seg = barrier_segment side (l ++ sub ++ r) ->
    False.
Proof.
    intros l sub r seg p q above side Hctx Hq Hneq Hy Hseed Habove Hqy Hsame.
    assert (Hwhole : l ++ sub ++ r <> []).
    { now apply whole_nonempty, context_sub_nonempty with (l := l) (r := r). }
    destruct (context_whole_embedded l sub r Hctx) as [ds [sc [_ Hembed]]].
  change (embed_scurve sc (l ++ sub ++ r)) in Hembed.
  destruct side.
  - cbn in Hseed, Hsame, Habove.
    destruct Hseed as [Hl [HpHead _]].
    subst p seg.
    destruct Hq as [Hq | Hq].
    + exfalso. apply Hneq. exact (eq_sym Hq).
    + assert (HheadNth :
          nth_error (l ++ sub ++ r) 0 = Some (hd_segment (l ++ sub ++ r))).
      { destruct (l ++ sub ++ r) as [|head tail]; [contradiction | reflexivity]. }
      destruct (embed_scurve_nth_embed sc (l ++ sub ++ r) Hembed 0
                  (hd_segment (l ++ sub ++ r)) HheadNth)
        as [[[v h] c] [_ HheadEmbed]].
      destruct v.
      * pose proof (embedded_head_trace_vertical_bound
                      (hd_segment (l ++ sub ++ r)) n h c
                      above HheadEmbed Habove) as Htop.
        rewrite Hq in Hqy. lra.
      * pose proof (s_end_relation
                      (hd_segment (l ++ sub ++ r)) h c HheadEmbed) as Hend.
        rewrite Hq in Hy. lra.
  - cbn in Hseed, Hsame, Habove.
    destruct Hseed as [Hr [HpLast _]].
    subst p seg.
    destruct Hq as [Hq | Hq].
    + set (last_i := (length (l ++ sub ++ r) - 1)%nat).
      assert (HlastNth :
          nth_error (l ++ sub ++ r) last_i =
            Some (last_segment (l ++ sub ++ r))).
      { unfold last_i. now apply nth_error_last. }
      destruct (embed_scurve_nth_embed sc (l ++ sub ++ r) Hembed last_i
                  (last_segment (l ++ sub ++ r)) HlastNth)
        as [[[v h] c] [_ HlastEmbed]].
      destruct v.
      * pose proof (n_end_relation
                      (last_segment (l ++ sub ++ r)) h c HlastEmbed) as Hend.
          rewrite Hq in Hy. lra.
      * pose proof (embedded_last_trace_vertical_bound
                      (last_segment (l ++ sub ++ r)) s h c
                      above HlastEmbed Habove) as Htop.
        rewrite Hq in Hqy. lra.
    + exfalso. apply Hneq. exact (eq_sym Hq).
Qed.

Lemma same_barrier_segment_upward_preserves_left_certificate :
  forall l sub r seg p q side,
    ClassificationContext l sub r ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    p <> q ->
    snd p <= snd q ->
    left_barrier_core side l sub r p ->
    snd q < snd (sub_left_anchor sub) ->
    seg = barrier_segment side (l ++ sub ++ r) ->
    (barrier_extension_seed l sub r side p
     \/ exists previous,
          barrier_reverse_step l sub r side previous p
          /\ left_up_certificate l sub r previous) ->
    left_up_certificate l sub r q.
(* 逆向き step 由来なら保存されている q の証明書を返す。延長線 seed
   由来なら、有限な end trace が q より上まで core を持つことに矛盾する。 *)
Proof.
    intros l sub r seg p q side Hctx Hp Hq Hneq Hy Hcore Hqy Hsame
      [Hseed | [previous [Hreverse Hprevious]]].
    - exfalso.
      pose proof Hcore as Hcore'.
      unfold left_barrier_core in Hcore'. cbn in Hcore'.
      destruct Hcore' as [_ [_ [_ [_ Hopen]]]].
      destruct (Hopen (snd (sub_left_anchor sub)) ltac:(lra))
        as [x [_ Habove]].
      eapply (extension_seed_barrier_trace_bounded_by_other_endpoint
                l sub r seg p q (x, snd (sub_left_anchor sub)) side);
        eauto; cbn; lra.
  - assert (Hqprevious : q = previous).
    { eapply barrier_reverse_step_other_endpoint; eauto. }
    now subst q.
Qed.

Lemma same_segment_upward_preserves_nondirect_left_certificate :
  forall l sub r seg p q side,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    snd p <= snd q ->
    left_barrier_core side l sub r p ->
    barrier_exception l sub r p ->
    on_barrier_trace side (l ++ sub ++ r) p ->
    left_up_certificate l sub r p ->
    (barrier_extension_seed l sub r side p
     \/ exists previous,
          barrier_reverse_step l sub r side previous p
          /\ left_up_certificate l sub r previous) ->
    fst q < fst (sub_left_anchor sub) ->
    snd q < snd (sub_left_anchor sub) ->
    left_up_certificate l sub r q.
Proof.
    intros l sub r seg p q side Hctx Hseg Hp Hq Hy Hcore
      Hexception Htrace Hcertificate Horigin Hqx Hqy.
  destruct (classic (p = q)) as [-> | Hneq].
  - exact Hcertificate.
  - pose proof (same_segment_left_exception_moves_outward_or_is_barrier
                  l sub r seg p q side Hctx Hseg Hp Hq Hneq Hy Hcore
                    Hexception Htrace Hqx Hqy) as [Hqxp | Hsame].
      + assert (Hylt : snd p < snd q).
        { exact (ordered_distinct_segment_endpoints_strict_y
                   seg p q Hp Hq Hneq Hy). }
        unfold left_barrier_core in Hcore. cbn in Hcore.
      destruct Hcore as [Hwhole [Hrising [Hpx [Hpy Hopen]]]].
      assert (Hlevel : left_barrier_at_level side l sub r q).
      { unfold left_barrier_at_level. cbn.
        destruct (Hopen (snd q) ltac:(lra)) as [x [[Hpxx Hxleft] Htraceq]].
        exists x. split; [lra | exact Htraceq]. }
        apply (left_certificate_at_level l sub r side q).
      unfold left_barrier_core. cbn.
      refine (conj Hwhole
                (conj Hrising (conj Hqx (conj Hqy _)))).
        intros y HyRange.
        destruct (Hopen y ltac:(lra)) as [x [[Hpxx Hxleft] Htracex]].
        exists x. split; [lra | exact Htracex].
        exact Hlevel.
      + exact (same_barrier_segment_upward_preserves_left_certificate
                 l sub r seg p q side Hctx Hp Hq Hneq Hy Hcore
                 Hqy Hsame Horigin).
Qed.

(* sub の x 範囲内で上側にいた端点から、同一セグメントが左 anchor の
   下へ抜けると、sub との上下関係が反転して交差する。 *)
Lemma same_segment_above_sub_cannot_exit_left_below :
  forall l sub r seg p q,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    snd p <= snd q ->
    in_sub_x_range sub p ->
    strictly_above_sub_at_x sub p ->
    fst q < fst (sub_left_anchor sub) ->
    snd q < snd (sub_left_anchor sub) ->
    False.
(* x の中間値点で seg と sub の上下順序が反転し、開性に反する。 *)
Admitted.

(* 右下の証明書を持つ点から同一セグメントで左下へ抜けると、右障壁を
   横切る。通常下端と例外下端は同じ open core で処理できる。 *)
Lemma right_certificate_blocks_same_segment_left_entry :
  forall l sub r seg p q,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    snd p <= snd q ->
    right_up_certificate l sub r p ->
    fst q < fst (sub_left_anchor sub) ->
    snd q < snd (sub_left_anchor sub) ->
    False.
Admitted.

(* sub の右外かつ右 anchor 以上から、左外かつ左 anchor 未満へ進む
   セグメントは、連結な x 単調 sub と交差する。 *)
Lemma same_segment_cannot_cross_sub_from_upper_right_to_lower_left :
  forall l sub r seg p q,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    fst (sub_right_anchor sub) < fst p ->
    snd (sub_right_anchor sub) <= snd p ->
    fst q < fst (sub_left_anchor sub) ->
    snd q < snd (sub_left_anchor sub) ->
    False.
(* 両 anchor の x で seg 上の点を取り、x_cross_h に還元する。 *)
Admitted.

(* 始点がまだ左側にない場合に、同一セグメントが左下へ入る遷移を扱う。 *)
Lemma same_segment_upward_enters_left_certificate :
  forall l sub r seg p q,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    snd p <= snd q ->
    up_path_invariant l sub r p ->
    fst (sub_left_anchor sub) <= fst p ->
    fst q < fst (sub_left_anchor sub) ->
    snd q < snd (sub_left_anchor sub) ->
    False.
Proof.
  intros l sub r seg p q Hctx Hseg Hp Hq Hy Hinv Hpx Hqx Hqy.
  destruct Hinv as [Hcenter [Hleft Hright]].
  pose proof (x_monotone_rect_x_bounds sub
                (context_sub_nonempty l sub r Hctx)
                (context_sub_connected l sub r Hctx)
                (context_sub_x_monotone l sub r Hctx)) as [Hrx0 Hrx1].
  destruct (Rle_dec (fst p) (fst (sub_right_anchor sub))) as [Hpr | Hpr].
  - eapply (same_segment_above_sub_cannot_exit_left_below
              l sub r seg p q Hctx Hseg Hp Hq Hy).
    + unfold in_sub_x_range. rewrite Hrx0, Hrx1.
      change (fst (sub_left_anchor sub) <= fst p <=
              fst (sub_right_anchor sub)). exact (conj Hpx Hpr).
    + apply Hcenter. unfold in_sub_x_range. rewrite Hrx0, Hrx1.
      change (fst (sub_left_anchor sub) <= fst p <=
              fst (sub_right_anchor sub)). exact (conj Hpx Hpr).
    + exact Hqx.
    + exact Hqy.
  - assert (Hpr' : fst (sub_right_anchor sub) < fst p) by lra.
    destruct (Rlt_dec (snd p) (snd (sub_right_anchor sub))) as [Hpy | Hpy].
    + eapply (right_certificate_blocks_same_segment_left_entry
                l sub r seg p q Hctx Hseg Hp Hq Hy).
      * exact (Hright Hpr' Hpy).
      * exact Hqx.
      * exact Hqy.
    + eapply (same_segment_cannot_cross_sub_from_upper_right_to_lower_left
                l sub r seg p q Hctx Hseg Hp Hq Hpr'); eauto; lra.
Qed.

Lemma same_segment_upward_preserves_left_certificate :
  forall l sub r seg p q,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    snd p <= snd q ->
    up_path_invariant l sub r p ->
    fst q < fst (sub_left_anchor sub) ->
    snd q < snd (sub_left_anchor sub) ->
    left_up_certificate l sub r q.
Proof.
  intros l sub r seg p q Hctx Hseg Hp Hq Hy Hinv Hqx Hqy.
    destruct Hinv as [Hcenter [Hleft Hright]].
    destruct (Rlt_dec (fst p) (fst (sub_left_anchor sub))) as [Hpx | Hpx].
    - assert (Hpy : snd p < snd (sub_left_anchor sub)) by lra.
      destruct (Hleft Hpx Hpy) as
        [side p Hcore Hlevel
        | side p Hcore Hseed Hblocks Htrace
        | side p previous Hcore Hreverse Hprevious Hblocks Htrace].
      + apply (same_segment_upward_preserves_direct_left_certificate
                 l sub r seg p q Hctx Hseg Hp Hq Hy); try assumption.
        exists side. now split.
      + exact (same_segment_upward_preserves_nondirect_left_certificate
                 l sub r seg p q side Hctx Hseg Hp Hq Hy Hcore
                 (or_introl (barrier_extension_seed_is_extension_up_seed
                                l sub r side p Hseed)) Htrace
                 (left_certificate_extension_seed
                    l sub r side p Hcore Hseed Hblocks Htrace)
                 (or_introl Hseed) Hqx Hqy).
      + exact (same_segment_upward_preserves_nondirect_left_certificate
                 l sub r seg p q side Hctx Hseg Hp Hq Hy Hcore
                 (or_intror (barrier_reverse_step_has_reverse_target
                                l sub r side previous p Hreverse))
                 Htrace
                 (left_certificate_reverse_step
                    l sub r side p previous Hcore Hreverse Hprevious Hblocks Htrace)
                 (or_intror (ex_intro _ previous (conj Hreverse Hprevious)))
                 Hqx Hqy).
  - exfalso.
    apply (same_segment_upward_enters_left_certificate
             l sub r seg p q Hctx Hseg Hp Hq Hy); try assumption.
    + repeat split; assumption.
    + lra.
Qed.

(* falling 障壁とは異なるセグメントについても、非隣接なら sparse、
   隣接なら dc により、上側端点は右外向きにしか進めない。 *)
Lemma distinct_segment_from_falling_barrier_moves_right :
  forall l sub r seg p q side,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    p <> q ->
    snd p <= snd q ->
    right_falling_barrier side (l ++ sub ++ r) ->
    on_barrier_trace side (l ++ sub ++ r) p ->
    (exists above,
        on_barrier_trace side (l ++ sub ++ r) above
        /\ snd p < snd above
        /\ fst above < fst p) ->
    seg <> barrier_segment side (l ++ sub ++ r) ->
    fst p < fst q.
Proof.
  intros l sub r seg p q side Hctx Hseg Hp Hq Hneq Hy Hfalling Htrace
    [above [Habove [Hpy Hpx]]] Hne.
  assert (Hylt : snd p < snd q).
  { exact (ordered_distinct_segment_endpoints_strict_y seg p q Hp Hq Hneq Hy). }
  set (whole := l ++ sub ++ r) in *.
  assert (Hwhole : whole <> []).
  { unfold whole. now apply whole_nonempty, context_sub_nonempty
      with (l := l) (r := r). }
  destruct (context_whole_embedded l sub r Hctx) as [ds [sc [_ Hembed]]].
  change (embed_scurve sc whole) in Hembed.
  destruct side.
  - cbn in Htrace, Habove, Hne, Hfalling.
    assert (HheadNth : nth_error whole 0 = Some (hd_segment whole)).
    { destruct whole as [|head tail]; [contradiction | reflexivity]. }
    destruct (embed_scurve_nth_embed sc whole Hembed 0
                (hd_segment whole) HheadNth)
      as [psHead [_ HembHead]].
    destruct (In_nth_error whole seg Hseg) as [i Hi].
    destruct Htrace as [t [Ht Htp]].
    destruct (Rlt_dec t 0) as [HtStrict | HtBody].
    + destruct (@nth_error_split Segment whole i seg Hi)
        as [before [after [Hsplit Hlen]]].
      destruct (context_sparse l sub r Hctx before seg after Hsplit)
        as [Hext _].
      exfalso. apply (Hext p).
      * left. split.
        -- intros Hnil. subst before. simpl in Hlen. subst i.
           rewrite HheadNth in Hi. injection Hi as Heq.
           apply Hne. exact (eq_sym Heq).
        -- unfold onHead_extend_strict. exists t. split; [exact HtStrict |].
           change (point (hd_segment (before ++ seg :: after)) t = p).
           rewrite <- Hsplit. exact Htp.
      * destruct Hp as [-> | ->];
          apply segment_in_rect_or_endpoints; [apply onInit | apply onTerm].
    + assert (HpHead : onSegment (hd_segment whole) p).
      { exists t. split; [lra | exact Htp]. }
      destruct i as [|i].
      * exfalso. apply Hne.
        rewrite HheadNth in Hi. now injection Hi as Heq.
      * destruct Hp as [HpInit | HpTerm].
        -- destruct i as [|i].
           ++ destruct (embed_scurve_adjacent_data
                         sc whole 0 (hd_segment whole) seg
                         Hembed HheadNth Hi)
                as [psSegHead [psSeg [HembHead' [HembSeg [Hdc Hjoin]]]]].
              assert (HpJoin : p = term (hd_segment whole)).
              { eapply adjacent_not_intersect_except_junction; eauto.
                rewrite HpInit. apply onInit. }
              destruct Hq as [HqInit | HqTerm].
              ** exfalso. apply Hneq. now rewrite HpInit, HqInit.
              ** pose proof (dc_after_falling_head_moves_right
                               psSegHead psSeg (hd_segment whole) seg above
                               Hdc HembHead' HembSeg
                               ltac:(rewrite <- HpInit, <- HqTerm; exact Hylt)
                               Habove ltac:(rewrite <- HpJoin; exact Hpy)
                               ltac:(rewrite <- HpJoin; exact Hpx)) as Hright.
                 now rewrite HpInit, HqTerm.
           ++ destruct (nth_error_far_in_nonadjacent_sides
                         whole (S (S i)) 0 seg (hd_segment whole)
                         Hi HheadNth ltac:(right; lia))
                as [before [after [Hsplit HinHead]]].
              destruct (context_sparse l sub r Hctx before seg after Hsplit)
                as [_ Hrect].
              exfalso. apply (Hrect (hd_segment whole) p HinHead).
              ** exact (segment_in_rect_or_endpoints _ _ HpHead).
              ** rewrite HpInit. apply segment_in_rect_or_endpoints, onInit.
        -- exfalso. eapply (later_body_point_not_on_earlier_segment
                     sc whole 0 (S i) (hd_segment whole) seg 1
                     Hembed (context_sparse l sub r Hctx)
                     HheadNth Hi ltac:(lia) ltac:(lra)).
           replace (point seg 1) with p by exact HpTerm.
           exact HpHead.
  - cbn in Htrace, Habove, Hne, Hfalling.
    set (last_i := (length whole - 1)%nat).
    assert (HlastNth : nth_error whole last_i = Some (last_segment whole)).
    { unfold last_i. now apply nth_error_last. }
    destruct (embed_scurve_nth_embed sc whole Hembed last_i
                (last_segment whole) HlastNth)
      as [psLast [_ HembLast]].
    destruct (In_nth_error whole seg Hseg) as [i Hi].
    assert (HiBound : (i <= last_i)%nat).
    { apply nth_error_lt in Hi. unfold last_i. lia. }
    destruct Htrace as [t [Ht Htp]].
    destruct (Rlt_dec 1 t) as [HtStrict | HtBody].
    + destruct (@nth_error_split Segment whole i seg Hi)
        as [before [after [Hsplit Hlen]]].
      destruct (context_sparse l sub r Hctx before seg after Hsplit)
        as [Hext _].
      exfalso. apply (Hext p).
      * right. split.
        -- intros Hnil. subst after. apply Hne. rewrite Hsplit.
           rewrite last_app_nonnil by discriminate. reflexivity.
        -- unfold onLast_extend_strict. exists t. split; [exact HtStrict |].
           change (point (last_segment (before ++ seg :: after)) t = p).
           rewrite <- Hsplit. exact Htp.
      * destruct Hp as [-> | ->];
          apply segment_in_rect_or_endpoints; [apply onInit | apply onTerm].
    + assert (HpLast : onSegment (last_segment whole) p).
      { exists t. split; [lra | exact Htp]. }
      destruct (Nat.eq_dec i last_i) as [Heq | Hlt].
      * exfalso. apply Hne.
        subst i. rewrite HlastNth in Hi. now injection Hi as Hsame.
      * assert (HiLt : (i < last_i)%nat) by lia.
        destruct Hp as [HpInit | HpTerm].
        -- exfalso. eapply (earlier_body_point_not_on_later_segment
                     sc whole i last_i seg (last_segment whole) 0
                     Hembed (context_sparse l sub r Hctx)
                     Hi HlastNth HiLt ltac:(lra)).
           replace (point seg 0) with p by exact HpInit.
           exact HpLast.
        -- destruct (Nat.eq_dec last_i (S i)) as [Hadj | Hfar].
           ++ destruct (embed_scurve_adjacent_data
                         sc whole i seg (last_segment whole)
                         Hembed Hi ltac:(now rewrite <- Hadj))
                as [psSeg [psLast' [HembSeg [HembLast' [Hdc Hjoin]]]]].
              assert (HpJoin : p = init (last_segment whole)).
              { rewrite <- Hjoin. exact HpTerm. }
              destruct Hq as [HqInit | HqTerm].
              ** pose proof (dc_before_falling_last_moves_right
                               psSeg psLast' seg (last_segment whole) above
                               Hdc HembSeg HembLast'
                               ltac:(rewrite <- HpTerm, <- HqInit; exact Hylt)
                               Habove ltac:(rewrite <- HpJoin; exact Hpy)
                               ltac:(rewrite <- HpJoin; exact Hpx)) as Hright.
                 now rewrite HpTerm, HqInit.
              ** exfalso. apply Hneq. now rewrite HpTerm, HqTerm.
           ++ assert (Hfar' : (S i < last_i)%nat) by lia.
              destruct (nth_error_far_in_nonadjacent_sides
                         whole i last_i seg (last_segment whole)
                         Hi HlastNth ltac:(left; exact Hfar'))
                as [before [after [Hsplit HinLast]]].
              destruct (context_sparse l sub r Hctx before seg after Hsplit)
                as [_ Hrect].
              exfalso. apply (Hrect (last_segment whole) p HinLast).
              ** exact (segment_in_rect_or_endpoints _ _ HpLast).
              ** rewrite HpTerm. apply segment_in_rect_or_endpoints, onTerm.
Qed.

Lemma same_segment_right_exception_moves_outward_or_is_barrier :
  forall l sub r seg p q side,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    p <> q ->
    snd p <= snd q ->
    right_barrier_core side l sub r p ->
    on_barrier_trace side (l ++ sub ++ r) p ->
    fst (sub_right_anchor sub) < fst q ->
    snd q < snd (sub_right_anchor sub) ->
    fst p < fst q
    \/ seg = barrier_segment side (l ++ sub ++ r).
(* 左側の双対。障壁自身でなければ、内向きの進行は隣接 dc に反する。 *)
Proof.
  intros l sub r seg p q side Hctx Hseg Hp Hq Hneq Hy Hcore Htrace Hqx Hqy.
  destruct (classic (seg = barrier_segment side (l ++ sub ++ r))) as [Heq | Hne].
  - now right.
  - left.
    pose proof Hcore as Hcore'.
    unfold right_barrier_core in Hcore'. cbn in Hcore'.
    destruct Hcore' as [Hwhole [Hfalling [Hpx [Hpy Hopen]]]].
    destruct (Hopen (snd (sub_right_anchor sub)) ltac:(lra))
      as [x [[Hxright Hxxp] Htracex]].
    apply (distinct_segment_from_falling_barrier_moves_right
             l sub r seg p q side Hctx Hseg Hp Hq Hneq Hy Hfalling Htrace).
    + exists (x, snd (sub_right_anchor sub)). repeat split; try assumption; cbn; lra.
    + exact Hne.
Qed.

Lemma same_barrier_segment_upward_preserves_right_certificate :
  forall l sub r seg p q side,
    ClassificationContext l sub r ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    p <> q ->
    snd p <= snd q ->
    right_barrier_core side l sub r p ->
    snd q < snd (sub_right_anchor sub) ->
    seg = barrier_segment side (l ++ sub ++ r) ->
    (barrier_extension_seed l sub r side p
     \/ exists previous,
          barrier_reverse_step l sub r side previous p
          /\ right_up_certificate l sub r previous) ->
    right_up_certificate l sub r q.
(* 左側の双対。逆向き起源なら保存された証明書へ戻り、延長線 seed
   起源なら有限な end trace と core の継続が矛盾する。 *)
Proof.
    intros l sub r seg p q side Hctx Hp Hq Hneq Hy Hcore Hqy Hsame
      [Hseed | [previous [Hreverse Hprevious]]].
    - exfalso.
      pose proof Hcore as Hcore'.
      unfold right_barrier_core in Hcore'. cbn in Hcore'.
      destruct Hcore' as [_ [_ [_ [_ Hopen]]]].
      destruct (Hopen (snd (sub_right_anchor sub)) ltac:(lra))
        as [x [_ Habove]].
      eapply (extension_seed_barrier_trace_bounded_by_other_endpoint
                l sub r seg p q (x, snd (sub_right_anchor sub)) side);
        eauto; cbn; lra.
  - assert (Hqprevious : q = previous).
    { eapply barrier_reverse_step_other_endpoint; eauto. }
    now subst q.
Qed.

Lemma same_segment_upward_preserves_nondirect_right_certificate :
  forall l sub r seg p q side,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    snd p <= snd q ->
    right_barrier_core side l sub r p ->
    on_barrier_trace side (l ++ sub ++ r) p ->
    right_up_certificate l sub r p ->
    (barrier_extension_seed l sub r side p
     \/ exists previous,
          barrier_reverse_step l sub r side previous p
          /\ right_up_certificate l sub r previous) ->
    fst (sub_right_anchor sub) < fst q ->
    snd q < snd (sub_right_anchor sub) ->
    right_up_certificate l sub r q.
Proof.
    intros l sub r seg p q side Hctx Hseg Hp Hq Hy Hcore
      Htrace Hcertificate Horigin Hqx Hqy.
    destruct (classic (p = q)) as [-> | Hneq].
    - exact Hcertificate.
	    - pose proof (same_segment_right_exception_moves_outward_or_is_barrier
	                  l sub r seg p q side Hctx Hseg Hp Hq Hneq Hy Hcore
                  Htrace Hqx Hqy) as [Hpxq | Hsame].
      + assert (Hylt : snd p < snd q).
        { exact (ordered_distinct_segment_endpoints_strict_y
                   seg p q Hp Hq Hneq Hy). }
        unfold right_barrier_core in Hcore. cbn in Hcore.
    destruct Hcore as [Hwhole [Hfalling [Hpx [Hpy Hopen]]]].
    assert (Hlevel : right_barrier_at_level side l sub r q).
    { unfold right_barrier_at_level. cbn.
      destruct (Hopen (snd q) ltac:(lra)) as [x [[Hxright Hxxp] Htraceq]].
      exists x. split; [lra | exact Htraceq]. }
      apply (right_certificate_at_level l sub r side q).
    unfold right_barrier_core. cbn.
    refine (conj Hwhole
              (conj Hfalling (conj Hqx (conj Hqy _)))).
      intros y HyRange.
      destruct (Hopen y ltac:(lra)) as [x [[Hxright Hxxp] Htracex]].
      exists x. split; [lra | exact Htracex].
      exact Hlevel.
      + exact (same_barrier_segment_upward_preserves_right_certificate
               l sub r seg p q side Hctx Hp Hq Hneq Hy Hcore
               Hqy Hsame Horigin).
Qed.

Lemma same_segment_upward_enters_right_certificate :
  forall l sub r seg p q,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    snd p <= snd q ->
    up_path_invariant l sub r p ->
    fst p <= fst (sub_right_anchor sub) ->
    fst (sub_right_anchor sub) < fst q ->
    snd q < snd (sub_right_anchor sub) ->
    False.
Admitted.

Lemma same_segment_upward_preserves_right_certificate :
  forall l sub r seg p q,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    snd p <= snd q ->
    up_path_invariant l sub r p ->
    fst (sub_right_anchor sub) < fst q ->
    snd q < snd (sub_right_anchor sub) ->
    right_up_certificate l sub r q.
Proof.
  intros l sub r seg p q Hctx Hseg Hp Hq Hy Hinv Hqx Hqy.
    destruct Hinv as [Hcenter [Hleft Hright]].
    destruct (Rlt_dec (fst (sub_right_anchor sub)) (fst p)) as [Hpx | Hpx].
    - assert (Hpy : snd p < snd (sub_right_anchor sub)) by lra.
      destruct (Hright Hpx Hpy) as
        [side p Hcore Hlevel
        | side p Hcore Hseed Hblocks Htrace
        | side p previous Hcore Hreverse Hprevious Hblocks Htrace].
      + apply (same_segment_upward_preserves_direct_right_certificate
                 l sub r seg p q Hctx Hseg Hp Hq Hy); try assumption.
        exists side. now split.
      + exact (same_segment_upward_preserves_nondirect_right_certificate
                 l sub r seg p q side Hctx Hseg Hp Hq Hy Hcore
                 Htrace
                 (right_certificate_extension_seed
                    l sub r side p Hcore Hseed Hblocks Htrace)
                 (or_introl Hseed) Hqx Hqy).
      + exact (same_segment_upward_preserves_nondirect_right_certificate
                 l sub r seg p q side Hctx Hseg Hp Hq Hy Hcore
                 Htrace
                 (right_certificate_reverse_step
                    l sub r side p previous Hcore Hreverse Hprevious Hblocks Htrace)
                 (or_intror (ex_intro _ previous (conj Hreverse Hprevious)))
                 Hqx Hqy).
  - exfalso.
    apply (same_segment_upward_enters_right_certificate
             l sub r seg p q Hctx Hseg Hp Hq Hy); try assumption.
    + repeat split; assumption.
    + lra.
Qed.

(* 同一セグメント上で低い端点から高い端点へ進む通常辺。 *)
Lemma same_segment_upward_preserves_up_path_invariant :
  forall l sub r seg p q,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    endpoint_of_seg seg p ->
    endpoint_of_seg seg q ->
    snd p <= snd q ->
    up_path_invariant l sub r p ->
    up_path_invariant l sub r q.
Proof.
  intros l sub r seg p q Hctx Hseg Hp Hq Hy Hinv.
  split.
  - now apply same_segment_upward_preserves_sub_above
      with (l := l) (r := r) (seg := seg) (p := p).
  - split.
    + now apply same_segment_upward_preserves_left_certificate
        with (seg := seg) (p := p).
    + now apply same_segment_upward_preserves_right_certificate
        with (seg := seg) (p := p).
Qed.

(* x 範囲が重なる非隣接セグメント間の、下側端点から上側端点への辺。 *)
Lemma nonadjacent_upward_preserves_up_path_invariant :
  forall l sub r i j s t ps pt,
    ClassificationContext l sub r ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (l ++ sub ++ r) j = Some t ->
    (S i < j \/ S j < i)%nat ->
    segment_x_ranges_overlap s t ->
    endpoint_of_seg s ps ->
    endpoint_of_seg t pt ->
    snd ps <= snd pt ->
    up_path_invariant l sub r ps ->
    up_path_invariant l sub r pt.
Admitted.

(* 傾き保存のために加えた四種類の逆向き辺を、一つの生成関係で扱う。 *)
Lemma barrier_reverse_step_preserves_up_path_invariant :
  forall l sub r side previous p,
    ClassificationContext l sub r ->
    barrier_reverse_step l sub r side previous p ->
    up_path_invariant l sub r previous ->
    up_path_invariant l sub r p.
Admitted.

(* 同じ x にある先頭・末尾延長線の上下比較を、その基点間へ移す二場合。 *)
Lemma head_below_last_preserves_up_path_invariant :
  forall l sub r ph pl,
    ClassificationContext l sub r ->
    onHead_extend (l ++ sub ++ r) ph ->
    onLast_extend (l ++ sub ++ r) pl ->
    fst ph = fst pl ->
    snd ph <= snd pl ->
    up_path_invariant l sub r
      (init (hd_segment (l ++ sub ++ r))) ->
    up_path_invariant l sub r
      (term (last_segment (l ++ sub ++ r))).
Admitted.

Lemma last_below_head_preserves_up_path_invariant :
  forall l sub r ph pl,
    ClassificationContext l sub r ->
    onHead_extend (l ++ sub ++ r) ph ->
    onLast_extend (l ++ sub ++ r) pl ->
    fst ph = fst pl ->
    snd pl <= snd ph ->
    up_path_invariant l sub r
      (term (last_segment (l ++ sub ++ r))) ->
    up_path_invariant l sub r
      (init (hd_segment (l ++ sub ++ r))).
Admitted.

(* 延長線と一セグメントの上下比較を、基点とその端点へ移す四場合。 *)
Lemma head_below_segment_preserves_up_path_invariant :
  forall l sub r seg e q p,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    onSegment seg e ->
    onHead_extend_strict (l ++ sub ++ r) q ->
    fst e = fst q ->
    snd q <= snd e ->
    endpoint_of_seg seg p ->
    up_path_invariant l sub r
      (init (hd_segment (l ++ sub ++ r))) ->
    up_path_invariant l sub r p.
Admitted.

Lemma segment_below_head_preserves_up_path_invariant :
  forall l sub r seg e q p,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    onSegment seg e ->
    onHead_extend_strict (l ++ sub ++ r) q ->
    fst e = fst q ->
    snd e <= snd q ->
    endpoint_of_seg seg p ->
    up_path_invariant l sub r p ->
    up_path_invariant l sub r
      (init (hd_segment (l ++ sub ++ r))).
Admitted.

Lemma last_below_segment_preserves_up_path_invariant :
  forall l sub r seg e q p,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    onSegment seg e ->
    onLast_extend_strict (l ++ sub ++ r) q ->
    fst e = fst q ->
    snd q <= snd e ->
    endpoint_of_seg seg p ->
    up_path_invariant l sub r
      (term (last_segment (l ++ sub ++ r))) ->
    up_path_invariant l sub r p.
Admitted.

Lemma segment_below_last_preserves_up_path_invariant :
  forall l sub r seg e q p,
    ClassificationContext l sub r ->
    In seg (l ++ sub ++ r) ->
    onSegment seg e ->
    onLast_extend_strict (l ++ sub ++ r) q ->
    fst e = fst q ->
    snd e <= snd q ->
    endpoint_of_seg seg p ->
    up_path_invariant l sub r p ->
    up_path_invariant l sub r
      (term (last_segment (l ++ sub ++ r))).
Admitted.

(* 以下の二命題が、今後埋める幾何学的な核心である。通常辺と
   Head/Last 由来の一辺を分け、経路全体の帰納から切り離す。 *)
Definition core_steps_preserve_up_invariant
    (l sub r : list Segment) : Prop :=
  forall p q,
    endpoint_core_step l sub r p q ->
    up_path_invariant l sub r p ->
    up_path_invariant l sub r q.

Definition core_paths_preserve_up_invariant
    (l sub r : list Segment) : Prop :=
  forall p q,
    endpoint_core_path l sub r p q ->
    up_path_invariant l sub r p ->
    up_path_invariant l sub r q.

Definition end_steps_preserve_up_invariant
    (l sub r : list Segment) : Prop :=
  forall p q,
    endpoint_end_step l sub r p q ->
    up_path_invariant l sub r p ->
    up_path_invariant l sub r q.

(* ----------------------------------------------------------------- *)
(*  一辺の保存則から有限パス全体への持ち上げ                       *)
(* ----------------------------------------------------------------- *)

(* 通常辺の二つの幾何補題を、core 一辺の保存則へまとめる。 *)
Lemma classification_context_core_steps_preserve_up_invariant :
  forall l sub r,
    ClassificationContext l sub r ->
    core_steps_preserve_up_invariant l sub r.
Proof.
  intros l sub r Hctx p q Hstep Hp.
  destruct Hstep as
      [seg p q Hin Hendpoint_p Hendpoint_q Hheight
      | i j s0 t ps pt Hs Ht Hfar Hover Hps Hpt Hheight].
  - eapply same_segment_upward_preserves_up_path_invariant.
    + exact Hctx.
    + exact Hin.
    + exact Hendpoint_p.
    + exact Hendpoint_q.
    + exact Hheight.
    + exact Hp.
  - eapply nonadjacent_upward_preserves_up_path_invariant.
    + exact Hctx.
    + exact Hs.
    + exact Ht.
    + exact Hfar.
    + exact Hover.
    + exact Hps.
    + exact Hpt.
    + exact Hheight.
    + exact Hp.
Qed.

(* 十種類の例外辺を、それぞれに対応する局所幾何補題から合成する。 *)
Lemma classification_context_end_steps_preserve_up_invariant :
  forall l sub r,
    ClassificationContext l sub r ->
    end_steps_preserve_up_invariant l sub r.
Proof.
  intros l sub r Hctx p q Hstep Hp.
  destruct Hstep.
  - eapply barrier_reverse_step_preserves_up_path_invariant; eauto.
    now apply barrier_reverse_head_north_cx with (hor := hor).
  - eapply barrier_reverse_step_preserves_up_path_invariant; eauto.
    now apply barrier_reverse_head_south_cc with (hor := hor).
  - eapply barrier_reverse_step_preserves_up_path_invariant; eauto.
    now apply barrier_reverse_last_north_cc with (hor := hor).
  - eapply barrier_reverse_step_preserves_up_path_invariant; eauto.
    now apply barrier_reverse_last_south_cx with (hor := hor).
  - eapply head_below_last_preserves_up_path_invariant; eauto.
  - eapply last_below_head_preserves_up_path_invariant; eauto.
  - eapply head_below_segment_preserves_up_path_invariant; eauto.
  - eapply segment_below_head_preserves_up_path_invariant; eauto.
  - eapply last_below_segment_preserves_up_path_invariant; eauto.
  - eapply segment_below_last_preserves_up_path_invariant; eauto.
Qed.

Lemma core_step_preservation_lifts_to_paths : forall l sub r,
  core_steps_preserve_up_invariant l sub r ->
  core_paths_preserve_up_invariant l sub r.
Proof.
  intros l sub r Hstep p q Hpath Hp.
  induction Hpath as [p | p next q Hfirst Htail IH].
  - exact Hp.
  - apply IH. now apply (Hstep p next Hfirst).
Qed.

(* core 区間と end 一辺の保存さえ得られれば、分解済み経路については
   純粋な関係の帰納だけで不変量が保存される。 *)
Lemma endpoint_factored_path_preserves_up_invariant : forall l sub r,
  core_paths_preserve_up_invariant l sub r ->
  end_steps_preserve_up_invariant l sub r ->
  forall p q,
    endpoint_factored_path l sub r p q ->
    up_path_invariant l sub r p ->
    up_path_invariant l sub r q.
Proof.
  intros l sub r Hcore Hend p q Hpath Hp.
  induction Hpath as
      [p q Hpath | p before after q Hprefix Hstep Htail IH].
  - exact (Hcore p q Hpath Hp).
  - apply IH.
    apply (Hend before after Hstep).
    exact (Hcore p before Hprefix Hp).
Qed.

Lemma endpoint_order_path_preserves_up_invariant : forall l sub r,
  core_paths_preserve_up_invariant l sub r ->
  end_steps_preserve_up_invariant l sub r ->
  forall p q,
    endpoint_order_path l sub r p q ->
    up_path_invariant l sub r p ->
    up_path_invariant l sub r q.
Proof.
  intros l sub r Hcore Hend p q Hpath Hp.
  eapply endpoint_factored_path_preserves_up_invariant; eauto.
  now apply endpoint_order_path_is_factored.
Qed.

(* 非隣接セグメントの端点は、閉長方形 sparse 性により sub 上にはない。 *)
(* ----------------------------------------------------------------- *)
(*  Up seed の非交差性と初期不変量                                 *)
(* ----------------------------------------------------------------- *)

Lemma nonadjacent_endpoint_not_on_sub : forall l sub r seg p,
  sparse_embedding (l ++ sub ++ r) ->
  In seg (nonadjacent_sides l r) ->
  endpoint_of_seg seg p ->
  ~ onSegmentlist sub p.
Proof.
  intros l sub r seg p Hsparse Hseg [-> | ->] Hsub.
  - eapply (sparse_nonadjacent_box_avoids_sub_points
              l sub r seg (init seg) Hsparse Hseg Hsub).
    apply segment_in_rect_or_endpoints, onInit.
  - eapply (sparse_nonadjacent_box_avoids_sub_points
              l sub r seg (term seg) Hsparse Hseg Hsub).
    apply segment_in_rect_or_endpoints, onTerm.
Qed.

(* セグメント本体を証人とする Up seed は sub 上の点にはならない。 *)
Lemma segment_up_seed_not_on_sub : forall l sub r p,
  sparse_embedding (l ++ sub ++ r) ->
  (exists seg q,
      In seg (nonadjacent_sides l r)
      /\ endpoint_of_seg seg p
      /\ onSegment seg q
      /\ in_sub_x_range sub q
      /\ above_sub_at_x sub q) ->
  ~ onSegmentlist sub p.
Proof.
  intros l sub r p Hsparse [seg [q [Hseg [Hp _]]]].
  exact (nonadjacent_endpoint_not_on_sub
           l sub r seg p Hsparse Hseg Hp).
Qed.

Local Lemma app_middle_assoc : forall (A : Type) (l sl : list A) t sr r,
  l ++ (sl ++ t :: sr) ++ r = (l ++ sl) ++ t :: (sr ++ r).
Proof.
  intros A l. induction l as [|x l IH]; intros sl t sr r; simpl.
  - induction sl as [|y sl IHsl]; simpl; [reflexivity | now rewrite IHsl].
  - now rewrite IH.
Qed.

Local Lemma nth_error_middle : forall (A : Type) (xs : list A) x ys,
  nth_error (xs ++ x :: ys) (length xs) = Some x.
Proof.
  intros. rewrite nth_error_app2 by apply Nat.le_refl.
  replace (length xs - length xs)%nat with 0%nat by lia.
  reflexivity.
Qed.

Local Lemma nth_error_middle_next : forall (A : Type) (xs : list A) x y ys,
  nth_error (xs ++ x :: y :: ys) (S (length xs)) = Some y.
Proof.
  intros. rewrite nth_error_app2 by lia.
  replace (S (length xs) - length xs)%nat with 1%nat by lia.
  reflexivity.
Qed.

(* l が空でなければ、全体の先頭始点は後続する sub 上へ戻らない。 *)
Lemma external_head_endpoint_not_on_sub : forall l sub r,
  ClassificationContext l sub r ->
  l <> [] ->
  ~ onSegmentlist sub (init (hd_segment (l ++ sub ++ r))).
Proof.
  intros l sub r Hctx Hl [t [Ht Hon]].
  destruct (in_app_app sub t Ht) as [sl [sr Hsub]].
  assert (HsubNorm : sl ++ [t] ++ sr = sl ++ t :: sr).
  { reflexivity. }
  rewrite HsubNorm in Hsub. subst sub.
  assert (Hwhole :
      l ++ (sl ++ t :: sr) ++ r = (l ++ sl) ++ t :: (sr ++ r)).
  { apply app_middle_assoc. }
  assert (Htarget :
      nth_error (l ++ (sl ++ t :: sr) ++ r) (length (l ++ sl)) = Some t).
  { rewrite Hwhole. apply nth_error_middle. }
  assert (Hhead :
      nth_error (l ++ (sl ++ t :: sr) ++ r) 0%nat =
      Some (hd_segment (l ++ (sl ++ t :: sr) ++ r))).
  { destruct l as [|a tail]; [contradiction | reflexivity]. }
  destruct (Nat.eq_dec (length (l ++ sl)) 1%nat) as [Hadj | Hfar].
  - (* 唯一の例外は singleton l と sub の先頭との直接隣接。 *)
    rewrite length_app in Hadj.
    assert (Hllen : length l <> 0%nat).
    { now rewrite length_zero_iff_nil. }
    assert (Hll : length l = 1%nat) by lia.
    assert (Hsl : length sl = 0%nat) by lia.
    apply length_zero_iff_nil in Hsl. subst sl.
    destruct l as [|a [|b tail]]; simpl in Hll; try lia.
    simpl in Hon, Hctx.
    destruct (context_whole_embedded [a] (t :: sr) r Hctx)
      as [ds [sc [_ Hembed]]].
    destruct (embed_scurve_adjacent_data
                sc ([a] ++ t :: sr ++ r) 0%nat a t Hembed eq_refl eq_refl)
      as [psa [pst [Ha [Ht' [Hdc Hjoin]]]]].
    pose proof (adjacent_not_intersect_except_junction
                  psa pst a t (init a) Hdc Ha Ht' Hjoin (onInit a) Hon) as Heq.
    exact (neq_init_term a Heq).
  - assert (Hprefix : (1 < length (l ++ sl))%nat).
    { assert (0 < length l)%nat by (destruct l; [contradiction | simpl; lia]).
      rewrite length_app in Hfar |- *. lia. }
    destruct (nth_error_far_in_nonadjacent_sides
                (l ++ (sl ++ t :: sr) ++ r)
                (length (l ++ sl)) 0%nat t
                (hd_segment (l ++ (sl ++ t :: sr) ++ r))
                Htarget Hhead ltac:(right; exact Hprefix))
      as [before [after [Hsplit Hin]]].
    destruct (context_sparse l (sl ++ t :: sr) r Hctx
                before t after Hsplit) as [_ Hrect].
    apply (Hrect (hd_segment (l ++ (sl ++ t :: sr) ++ r))
             (init (hd_segment (l ++ (sl ++ t :: sr) ++ r))) Hin).
    + apply segment_in_rect_or_endpoints, onInit.
    + change (in_segment_rect_or_endpoints t
        (init (hd_segment (l ++ (sl ++ t :: sr) ++ r)))).
      now apply segment_in_rect_or_endpoints.
Qed.

(* r が空でなければ、全体の末尾終点は先行する sub 上へ戻らない。 *)
Lemma external_last_endpoint_not_on_sub : forall l sub r,
  ClassificationContext l sub r ->
  r <> [] ->
  ~ onSegmentlist sub (term (last_segment (l ++ sub ++ r))).
Proof.
  intros l sub r Hctx Hr [t [Ht Hon]].
  destruct (in_app_app sub t Ht) as [sl [sr Hsub]].
  assert (HsubNorm : sl ++ [t] ++ sr = sl ++ t :: sr) by reflexivity.
  rewrite HsubNorm in Hsub. subst sub.
  assert (Hwhole :
      l ++ (sl ++ t :: sr) ++ r = (l ++ sl) ++ t :: (sr ++ r)).
  { apply app_middle_assoc. }
  set (whole := l ++ (sl ++ t :: sr) ++ r).
  set (target_index := length (l ++ sl)).
  set (last_index := (length whole - 1)%nat).
  assert (HwholeNe : whole <> []).
  { unfold whole. intros Hnil. apply app_eq_nil in Hnil as [_ Hnil].
    apply app_eq_nil in Hnil as [_ Hnil]. contradiction. }
  assert (Htarget : nth_error whole target_index = Some t).
  { unfold whole, target_index. rewrite Hwhole. apply nth_error_middle. }
  assert (Hlast : nth_error whole last_index = Some (last_segment whole)).
  { unfold last_index, last_segment. now apply nth_error_last. }
  destruct (Nat.eq_dec (length (sr ++ r)) 1%nat) as [Hadj | Hfar].
  - (* 唯一の例外は sub の末尾と singleton r との直接隣接。 *)
    rewrite length_app in Hadj.
    assert (Hrlen : length r <> 0%nat).
    { now rewrite length_zero_iff_nil. }
    assert (Hrr : length r = 1%nat) by lia.
    assert (Hsr : length sr = 0%nat) by lia.
    apply length_zero_iff_nil in Hsr. subst sr.
    destruct r as [|a [|b tail]]; simpl in Hrr; try lia.
    simpl in Hon, Hctx, whole, last_index, Htarget, Hlast.
    destruct (context_whole_embedded l (sl ++ [t]) [a] Hctx)
      as [ds [sc [_ Hembed]]].
    pose proof (app_middle_assoc Segment l sl t [] [a]) as Hwhole2.
    simpl in Hwhole2.
    assert (Hnext :
      nth_error (l ++ (sl ++ [t]) ++ [a]) (S (length (l ++ sl))) = Some a).
    { rewrite Hwhole2. apply nth_error_middle_next. }
    assert (Htarget' :
      nth_error (l ++ (sl ++ [t]) ++ [a]) (length (l ++ sl)) = Some t).
    { rewrite Hwhole2. apply nth_error_middle. }
    destruct (embed_scurve_adjacent_data
                sc (l ++ (sl ++ [t]) ++ [a]) (length (l ++ sl)) t a
                Hembed Htarget' Hnext)
      as [pst [psa [Ht' [Ha [Hdc Hjoin]]]]].
    assert (Hlastseg : last_segment (l ++ (sl ++ [t]) ++ [a]) = a).
    { assert (Htail : (sl ++ [t]) ++ [a] <> []).
      { intros Hnil. pose proof (f_equal (@length Segment) Hnil).
        rewrite !length_app in H. simpl in H. lia. }
      rewrite (last_app_nonnil l ((sl ++ [t]) ++ [a])) by exact Htail.
      rewrite (last_app_nonnil (sl ++ [t]) [a]) by discriminate.
      reflexivity. }
    rewrite Hlastseg in Hon.
    pose proof (adjacent_not_intersect_except_junction
                  pst psa t a (term a) Hdc Ht' Ha Hjoin Hon (onTerm a)) as Heq.
    apply (neq_init_term a). rewrite <- Hjoin, <- Heq. reflexivity.
  - assert (Hsuffix : (1 < length (sr ++ r))%nat).
    { assert (0 < length r)%nat by (destruct r; [contradiction | simpl; lia]).
      rewrite length_app in Hfar |- *. lia. }
    assert (Hindices : (S target_index < last_index)%nat).
    { unfold target_index, last_index, whole.
      rewrite Hwhole, !length_app. simpl. lia. }
    destruct (nth_error_far_in_nonadjacent_sides
                whole target_index last_index t (last_segment whole)
                Htarget Hlast ltac:(left; exact Hindices))
      as [before [after [Hsplit Hin]]].
    destruct (context_sparse l (sl ++ t :: sr) r Hctx
                before t after Hsplit) as [_ Hrect].
    apply (Hrect (last_segment whole) (term (last_segment whole)) Hin).
    + apply segment_in_rect_or_endpoints, onTerm.
    + change (in_segment_rect_or_endpoints t (term (last_segment whole))).
      now apply segment_in_rect_or_endpoints.
Qed.

Lemma segment_down_seed_not_on_sub : forall l sub r p,
  sparse_embedding (l ++ sub ++ r) ->
  (exists seg q,
      In seg (nonadjacent_sides l r)
      /\ endpoint_of_seg seg p
      /\ onSegment seg q
      /\ in_sub_x_range sub q
      /\ below_sub_at_x sub q) ->
  ~ onSegmentlist sub p.
Proof.
  intros l sub r p Hsparse [seg [q [Hseg [Hp _]]]].
  exact (nonadjacent_endpoint_not_on_sub
           l sub r seg p Hsparse Hseg Hp).
Qed.

(* 各 seed は、閉長方形 sparse 性と非空側条件により sub 上にはない。 *)
Lemma endpoint_up_seed_not_on_sub : forall l sub r p,
  ClassificationContext l sub r ->
  endpoint_up_seed l sub r p ->
  ~ onSegmentlist sub p.
Proof.
  intros l sub r p Hctx [_ [Hsegment | [[Hl [-> _]] | [Hr [-> _]]]]].
  - exact (segment_up_seed_not_on_sub
             l sub r p (context_sparse l sub r Hctx) Hsegment).
  - exact (external_head_endpoint_not_on_sub l sub r Hctx Hl).
  - exact (external_last_endpoint_not_on_sub l sub r Hctx Hr).
Qed.

Lemma endpoint_down_seed_not_on_sub : forall l sub r p,
  ClassificationContext l sub r ->
  endpoint_down_seed l sub r p ->
  ~ onSegmentlist sub p.
Proof.
  intros l sub r p Hctx [_ [Hsegment | [[Hl [-> _]] | [Hr [-> _]]]]].
  - exact (segment_down_seed_not_on_sub
             l sub r p (context_sparse l sub r Hctx) Hsegment).
  - exact (external_head_endpoint_not_on_sub l sub r Hctx Hl).
  - exact (external_last_endpoint_not_on_sub l sub r Hctx Hr).
Qed.

Lemma strict_extension_not_on_sub : forall l sub r p,
  sparse_embedding (l ++ sub ++ r) ->
  ((l <> [] /\ onHead_extend_strict (l ++ sub ++ r) p)
   \/ (r <> [] /\ onLast_extend_strict (l ++ sub ++ r) p)) ->
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
  - destruct Hextend as [[Hl Hhead] | [Hr Hlast]].
    + left. split.
      * intros Hnil. apply app_eq_nil in Hnil. tauto.
      * now rewrite <- Hwhole.
    + right. split.
      * intros Hnil. apply app_eq_nil in Hnil. tauto.
      * now rewrite <- Hwhole.
  - change (in_segment_rect_or_endpoints seg p).
    now apply segment_in_rect_or_endpoints.
Qed.

Lemma nonadjacent_body_trace_disjoint_from_sub : forall l sub r seg,
  sparse_embedding (l ++ sub ++ r) ->
  In seg (nonadjacent_sides l r) ->
  trace_disjoint_from_segmentlist TraceBody seg sub.
Proof.
  intros l sub r seg Hsparse Hseg p Hp Hsub.
  apply (sparse_nonadjacent_box_avoids_sub_points
           l sub r seg p Hsparse Hseg Hsub).
  change (in_segment_rect_or_endpoints seg p).
  now apply segment_in_rect_or_endpoints.
Qed.

Lemma external_head_trace_disjoint_from_sub : forall l sub r,
  ClassificationContext l sub r ->
  l <> [] ->
  trace_disjoint_from_segmentlist
    TraceHead (hd_segment (l ++ sub ++ r)) sub.
Proof.
  intros l sub r Hctx Hl p [t [Ht Hpoint]] Hsub.
  destruct (Rlt_dec t 0) as [Hstrict | Hbase].
  - eapply strict_extension_not_on_sub; eauto using context_sparse.
    left. split; [exact Hl |].
    exists t. split; assumption.
  - assert (Ht0 : t = 0) by lra. subst t.
    change (init (hd_segment (l ++ sub ++ r)) = p) in Hpoint.
    subst p.
    exact (external_head_endpoint_not_on_sub l sub r Hctx Hl Hsub).
Qed.

Lemma external_last_trace_disjoint_from_sub : forall l sub r,
  ClassificationContext l sub r ->
  r <> [] ->
  trace_disjoint_from_segmentlist
    TraceLast (last_segment (l ++ sub ++ r)) sub.
Proof.
  intros l sub r Hctx Hr p [t [Ht Hpoint]] Hsub.
  destruct (Rlt_dec 1 t) as [Hstrict | Hbase].
  - eapply strict_extension_not_on_sub; eauto using context_sparse.
    right. split; [exact Hr |].
    exists t. split; assumption.
  - assert (Ht1 : t = 1) by lra. subst t.
    change (term (last_segment (l ++ sub ++ r)) = p) in Hpoint.
    subst p.
    exact (external_last_endpoint_not_on_sub l sub r Hctx Hr Hsub).
Qed.

(* 三種類の Up seed はいずれも、sub の上側にある非交差 trace を
   持つ。trace は中央での上下関係にだけ使い、左右の障壁の代用にはしない。 *)
Lemma endpoint_up_seed_has_trace : forall l sub r p,
  ClassificationContext l sub r ->
  endpoint_up_seed l sub r p ->
  on_trace_above_sub sub p.
Proof.
  intros l sub r p Hctx Hseed.
  destruct Hseed as [_ [Hbody | [Hhead | Hlast]]].
  - destruct Hbody as
      [seg [q [Hseg [Hp [Hq [_ [z [Hz [Hx Hy]]]]]]]]].
    exists TraceBody, seg, q, z. repeat split; try assumption.
    + now apply nonadjacent_body_trace_disjoint_from_sub
        with (l := l) (r := r); [apply context_sparse |].
    + destruct Hp as [-> | ->]; [apply onInit | apply onTerm].
  - destruct Hhead as [Hl [-> [q [z [Hq [Hz [Hx Hy]]]]]]].
    exists TraceHead, (hd_segment (l ++ sub ++ r)), q, z.
    repeat split; try assumption.
    + now apply external_head_trace_disjoint_from_sub.
    + unfold onSegmentTrace, onHead. exists 0. split; [lra | reflexivity].
    + destruct Hq as [t [Ht Htq]].
      unfold onSegmentTrace, onHead. exists t. split; [lra | exact Htq].
  - destruct Hlast as [Hr [-> [q [z [Hq [Hz [Hx Hy]]]]]]].
    exists TraceLast, (last_segment (l ++ sub ++ r)), q, z.
    repeat split; try assumption.
    + now apply external_last_trace_disjoint_from_sub.
    + unfold onSegmentTrace, onLast. exists 1. split; [lra | reflexivity].
    + destruct Hq as [t [Ht Htq]].
      unfold onSegmentTrace, onLast. exists t. split; [lra | exact Htq].
Qed.

(* body seed の端点が init sub より左下にあると、sub の x 範囲で
   その上へ至るまでに端点長方形が sub 上の点を含み、閉長方形
   sparse 性に反する。 *)
Lemma body_up_seed_cannot_be_left_below : forall l sub r p,
  ClassificationContext l sub r ->
  (exists seg q,
      In seg (nonadjacent_sides l r)
      /\ endpoint_of_seg seg p
      /\ onSegment seg q
      /\ in_sub_x_range sub q
      /\ above_sub_at_x sub q) ->
  fst p < fst (sub_left_anchor sub) ->
  snd p < snd (sub_left_anchor sub) ->
  False.
Admitted.

(* 左下に残り得る延長線 seed からは、次の一辺で sub 以下の
   危険点へ出られない。 *)
Lemma extension_up_seed_locally_blocks_unsafe_up : forall l sub r p,
  ClassificationContext l sub r ->
  extension_up_seed l sub r p ->
  fst p < fst (sub_left_anchor sub) ->
  snd p < snd (sub_left_anchor sub) ->
  locally_blocks_unsafe_up l sub r p.
Proof.
  intros l sub r p Hctx Hseed _ _.
  apply barrier_exception_locally_blocks_unsafe_up; [exact Hctx |].
  now left.
Qed.

(* 左下の Up seed は body seed ではあり得ず、必ず延長線 seed である。 *)
Lemma endpoint_up_seed_left_low_is_extension_seed : forall l sub r p,
  ClassificationContext l sub r ->
  endpoint_up_seed l sub r p ->
  fst p < fst (sub_left_anchor sub) ->
  snd p < snd (sub_left_anchor sub) ->
  extension_up_seed l sub r p.
Proof.
  intros l sub r p Hctx [_ [Hbody | [Hhead | Hlast]]] Hx Hy.
  - exfalso.
    exact (body_up_seed_cannot_be_left_below
             l sub r p Hctx Hbody Hx Hy).
  - left. exact Hhead.
  - right. exact Hlast.
Qed.

(* 左下の extension seed を通る同じ end trace は、seed より上で
   init sub まで続く open core を与える。 *)
Lemma extension_up_seed_has_left_barrier_core : forall l sub r p,
  ClassificationContext l sub r ->
  extension_up_seed l sub r p ->
  fst p < fst (sub_left_anchor sub) ->
  snd p < snd (sub_left_anchor sub) ->
  exists side,
    left_barrier_core side l sub r p
    /\ barrier_extension_seed l sub r side p
    /\ on_barrier_trace side (l ++ sub ++ r) p.
Admitted.

Lemma endpoint_up_seed_has_left_certificate : forall l sub r p,
  ClassificationContext l sub r ->
  endpoint_up_seed l sub r p ->
  fst p < fst (sub_left_anchor sub) ->
  snd p < snd (sub_left_anchor sub) ->
  left_up_certificate l sub r p.
Proof.
  intros l sub r p Hctx Hseed Hx Hy.
  assert (Hextension : extension_up_seed l sub r p).
  { now eapply endpoint_up_seed_left_low_is_extension_seed. }
    destruct (extension_up_seed_has_left_barrier_core
                l sub r p Hctx Hextension Hx Hy)
      as [side [Hcore [HbarrierSeed Htrace]]].
    apply (left_certificate_extension_seed l sub r side p Hcore HbarrierSeed).
    - now eapply extension_up_seed_locally_blocks_unsafe_up.
    - exact Htrace.
Qed.

(* 右側も双対で、body seed は障壁を作り、延長線 seed だけを
   局所的な進出禁止で扱う。 *)
Lemma endpoint_up_seed_has_right_certificate : forall l sub r p,
  ClassificationContext l sub r ->
  endpoint_up_seed l sub r p ->
  fst (sub_right_anchor sub) < fst p ->
  snd p < snd (sub_right_anchor sub) ->
  right_up_certificate l sub r p.
Admitted.

Lemma endpoint_up_seed_satisfies_up_path_invariant : forall l sub r p,
  ClassificationContext l sub r ->
  endpoint_up_seed l sub r p ->
  up_path_invariant l sub r p.
Proof.
  intros l sub r p Hctx Hseed.
  assert (Htrace : on_trace_above_sub sub p).
  { now apply endpoint_up_seed_has_trace with (l := l) (r := r). }
  assert (Habove : strictly_above_sub_at_x sub p).
  { eapply on_trace_above_sub_implies_strictly_above_at_x; eauto using
      context_sub_nonempty, context_sub_connected, context_sub_x_monotone. }
  split.
  - intros _. exact Habove.
  - split; intros Hx Hy.
    + now apply endpoint_up_seed_has_left_certificate.
    + now apply endpoint_up_seed_has_right_certificate.
Qed.

(* Up は順序の上向き、Down は順序の下向きへ閉じる。 *)
(* ----------------------------------------------------------------- *)
(*  順序閉包からの具体的な端点分類器                               *)
(* ----------------------------------------------------------------- *)

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

(* Up と Down の source を結ぶ順序パスは、固定部分 sub を通る。 *)
Axiom endpoint_order_up_down_path_meets_sub :
  forall l sub r,
    ClassificationContext l sub r ->
    forall upper lower,
      endpoint_up_seed l sub r upper ->
      endpoint_down_seed l sub r lower ->
      endpoint_order_path l sub r upper lower ->
      exists at_sub,
        onSegmentlist sub at_sub
        /\ endpoint_order_path l sub r upper at_sub
        /\ endpoint_order_path l sub r at_sub lower.

(* 幾何学的な核心：Up 用不変量は、通常辺と Head/Last 由来の例外辺を
   任意に組み合わせた順序経路の全体で保存される。 *)
Lemma up_path_invariant_preserved_by_order_path :
  forall l sub r,
    ClassificationContext l sub r ->
    forall p q,
      up_path_invariant l sub r p ->
      endpoint_order_path l sub r p q ->
      up_path_invariant l sub r q.
Proof.
  intros l sub r Hctx p q Hp Hpath.
  eapply endpoint_order_path_preserves_up_invariant; eauto.
  - apply core_step_preservation_lifts_to_paths.
    now apply classification_context_core_steps_preserve_up_invariant.
  - now apply classification_context_end_steps_preserve_up_invariant.
Qed.

(* Up source から sub 外だけを通ってきたパスは、次の一辺で初めて
   sub へ入ることができない。共通 x 区間の上下不変性と、その区間を
   外れた部分での端点順序を組み合わせて示す。 *)
Lemma endpoint_order_up_first_sub_entry_impossible :
  forall l sub r,
    ClassificationContext l sub r ->
    forall upper before at_sub,
      endpoint_up_seed l sub r upper ->
      endpoint_order_path l sub r upper before ->
      ~ onSegmentlist sub before ->
      endpoint_order_step l sub r before at_sub ->
      onSegmentlist sub at_sub ->
      False.
Proof.
  intros l sub r Hctx upper before at_sub
    Hseed Hprefix _ Hstep Hat_sub.
  assert (Hlast : endpoint_order_path l sub r before at_sub).
  { eapply Stdlib.Relations.Relation_Operators.rt1n_trans.
    - exact Hstep.
    - apply Stdlib.Relations.Relation_Operators.rt1n_refl. }
  assert (Hpath : endpoint_order_path l sub r upper at_sub).
  { eapply endpoint_order_path_trans; eauto. }
  assert (Hinitial : up_path_invariant l sub r upper).
  { now apply endpoint_up_seed_satisfies_up_path_invariant. }
  assert (Hfinal : up_path_invariant l sub r at_sub).
  { eapply up_path_invariant_preserved_by_order_path; eauto. }
  exact (up_path_invariant_not_on_sub
           l sub r at_sub Hctx Hfinal Hat_sub).
Qed.

(* sub 上から出た順序パスは、sub 外だけを通って Down source へ
   到達できない。末尾側まで含む下側の局所的な障壁補題である。 *)
Axiom endpoint_order_sub_first_exit_to_down_impossible :
  forall l sub r,
    ClassificationContext l sub r ->
    forall before after lower,
      onSegmentlist sub before ->
      endpoint_order_step l sub r before after ->
      ~ onSegmentlist sub after ->
      endpoint_order_path l sub r after lower ->
      endpoint_down_seed l sub r lower ->
      False.

Lemma endpoint_order_up_path_not_reaches_sub :
  forall l sub r,
    ClassificationContext l sub r ->
    forall upper lower,
      endpoint_up_seed l sub r upper ->
      onSegmentlist sub lower ->
      ~ endpoint_order_path l sub r upper lower.
Proof.
  intros l sub r Hctx upper lower Hup Hlower Hpath.
  destruct (endpoint_order_path_first_sub_entry
              l sub r upper lower Hpath
              (endpoint_up_seed_not_on_sub l sub r upper Hctx Hup) Hlower)
    as [before [at_sub [Hprefix [Hstep [Hbefore [Hat _]]]]]].
  exact (endpoint_order_up_first_sub_entry_impossible
           l sub r Hctx upper before at_sub Hup Hprefix Hbefore Hstep Hat).
Qed.

Lemma endpoint_order_sub_path_not_reaches_down :
  forall l sub r,
    ClassificationContext l sub r ->
    forall upper lower,
      onSegmentlist sub upper ->
      endpoint_down_seed l sub r lower ->
      ~ endpoint_order_path l sub r upper lower.
Proof.
  intros l sub r Hctx upper lower Hupper Hdown Hpath.
  destruct (endpoint_order_path_first_exit
              l sub r (onSegmentlist sub) upper lower Hpath Hupper
              (endpoint_down_seed_not_on_sub l sub r lower Hctx Hdown))
    as [before [after [Hprefix [Hstep [Hbefore [Hafter Hsuffix]]]]]].
  exact (endpoint_order_sub_first_exit_to_down_impossible
           l sub r Hctx before after lower Hbefore Hstep Hafter Hsuffix Hdown).
Qed.

(* 三つの幾何学的障壁を合成した、従来の source 分離命題。 *)
Lemma endpoint_order_path_separates_sources :
  forall l sub r,
    ClassificationContext l sub r ->
    forall upper lower,
      ((endpoint_up_seed l sub r upper
        /\ (endpoint_down_seed l sub r lower
            \/ onSegmentlist sub lower))
       \/ (onSegmentlist sub upper
           /\ endpoint_down_seed l sub r lower)) ->
      ~ endpoint_order_path l sub r upper lower.
Proof.
  intros l sub r Hctx upper lower
    [[Hup [Hdown | Hsub]] | [Hsub Hdown]] Hpath.
  - destruct (endpoint_order_up_down_path_meets_sub
                l sub r Hctx upper lower Hup Hdown Hpath)
      as [at_sub [Hat [Hprefix _]]].
    exact (endpoint_order_up_path_not_reaches_sub
             l sub r Hctx upper at_sub Hup Hat Hprefix).
  - exact (endpoint_order_up_path_not_reaches_sub
             l sub r Hctx upper lower Hup Hsub Hpath).
  - exact (endpoint_order_sub_path_not_reaches_down
             l sub r Hctx upper lower Hsub Hdown Hpath).
Qed.

(* 推移閉包の表現の違いは上の幾何補題から切り離す。 *)
Lemma endpoint_order_separates_sources :
  forall l sub r,
    ClassificationContext l sub r ->
    forall upper lower,
      ((endpoint_up_seed l sub r upper
        /\ (endpoint_down_seed l sub r lower
            \/ onSegmentlist sub lower))
       \/ (onSegmentlist sub upper
           /\ endpoint_down_seed l sub r lower)) ->
      ~ endpoint_order l sub r upper lower.
Proof.
  intros l sub r Hctx upper lower Hsources Horder.
  apply (endpoint_order_path_separates_sources
           l sub r Hctx upper lower Hsources).
  now apply (proj1 (endpoint_order_path_iff l sub r upper lower)).
Qed.

(* 三種類の到達不能性を独立した名前で公開し、以後の証明が大きな論理和に
   依存しないようにする。 *)
Lemma up_seed_not_reaches_down_seed : forall l sub r,
  ClassificationContext l sub r ->
  forall upper lower,
    endpoint_up_seed l sub r upper ->
    endpoint_down_seed l sub r lower ->
    ~ endpoint_order l sub r upper lower.
Proof.
  intros l sub r Hctx upper lower Hup Hdown.
  now apply (endpoint_order_separates_sources l sub r Hctx upper lower),
    or_introl; split; [exact Hup | left].
Qed.

Lemma up_seed_not_reaches_sub : forall l sub r,
  ClassificationContext l sub r ->
  forall upper lower,
    endpoint_up_seed l sub r upper ->
    onSegmentlist sub lower ->
    ~ endpoint_order l sub r upper lower.
Proof.
  intros l sub r Hctx upper lower Hup Hsub.
  now apply (endpoint_order_separates_sources l sub r Hctx upper lower),
    or_introl; split; [exact Hup | right].
Qed.

Lemma sub_not_reaches_down_seed : forall l sub r,
  ClassificationContext l sub r ->
  forall upper lower,
    onSegmentlist sub upper ->
    endpoint_down_seed l sub r lower ->
    ~ endpoint_order l sub r upper lower.
Proof.
  intros l sub r Hctx upper lower Hsub Hdown.
  now apply (endpoint_order_separates_sources l sub r Hctx upper lower),
    or_intror.
Qed.

(* 上の分離補題により、一点が Up/Down の双方から強制されることはない。 *)
Lemma endpoint_forcing_disjoint :
  forall l sub r,
    ClassificationContext l sub r ->
    forall p,
      ~ (endpoint_forced_up l sub r p
         /\ endpoint_forced_down l sub r p).
Proof.
  intros l sub r Hctx p [[up [Hup Hupp]] [down [Hdown Hpdown]]].
  apply (up_seed_not_reaches_down_seed
           l sub r Hctx up down Hup Hdown).
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
    exact (up_seed_not_reaches_sub
             l sub r Hctx up p Hup Hsub Horder).
  - intros [down [Hdown Horder]].
    exact (sub_not_reaches_down_seed
             l sub r Hctx p down Hsub Hdown Horder).
Qed.

(* 元のセグメント自身が、元の両端点・向き・両傾きによる再接続を与える。 *)
(* ----------------------------------------------------------------- *)
(*  分類された先頭・末尾の傾き保存                                 *)
(* ----------------------------------------------------------------- *)

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
      apply rt_step. apply order_end_step.
      eapply order_head_north_cx_reverse; eauto.
    + eapply endpoint_order_classified; eauto.
      apply rt_step. apply order_core_step.
      eapply order_on_segment with (seg := seg).
      * now left.
      * now left.
      * now right.
      * pose proof (n_end_relation seg hor cx Hembed). lra.
  - (* north, concave: the start moves weakly down relative to the end. *)
    apply classified_init_slope_relative_lower; [exact Hh | |].
    + eapply endpoint_order_classified; eauto.
      apply rt_step. apply order_core_step.
      eapply order_on_segment with (seg := seg).
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
      apply rt_step. apply order_core_step.
      eapply order_on_segment with (seg := seg).
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
      apply rt_step. apply order_core_step.
      eapply order_on_segment with (seg := seg).
      * now left.
      * now right.
      * now left.
      * pose proof (s_end_relation seg hor cc Hembed). lra.
    + eapply endpoint_order_classified; eauto.
      apply rt_step. apply order_end_step.
      eapply order_head_south_cc_reverse; eauto.
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
      apply rt_step. apply order_core_step.
      eapply order_on_segment with (seg := seg).
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
      apply rt_step. apply order_end_step.
      eapply order_last_north_cc_reverse; eauto.
    + eapply endpoint_order_classified; eauto.
      apply rt_step. apply order_core_step.
      eapply order_on_segment with (seg := seg).
      * exact HinWhole.
      * now left.
      * now right.
      * pose proof (n_end_relation seg hor cc Hembed). lra.
  - (* south, convex: the added reverse constraint forces equal regions. *)
    apply classified_term_slope_same_region.
    apply region_at_or_above_antisym.
    + eapply endpoint_order_classified; eauto.
      apply rt_step. apply order_core_step.
      eapply order_on_segment with (seg := seg).
      * exact HinWhole.
      * now right.
      * now left.
      * pose proof (s_end_relation seg hor cx Hembed). lra.
    + eapply endpoint_order_classified; eauto.
      apply rt_step. apply order_end_step.
      eapply order_last_south_cx_reverse; eauto.
  - (* south, concave: the end moves weakly down relative to the start. *)
    apply classified_term_slope_relative_lower; [exact Hh | |].
    + eapply endpoint_order_classified; eauto.
      apply rt_step. apply order_core_step.
      eapply order_on_segment with (seg := seg).
      * exact HinWhole.
      * now right.
      * now left.
      * pose proof (s_end_relation seg hor cc Hembed). lra.
    + destruct hor.
      * intros p Hx Hy. eapply southeast_cc_lower_term_slope; eauto.
      * intros p Hx Hy. eapply southwest_cc_lower_term_slope; eauto.
Qed.

(* ----------------------------------------------------------------- *)
(*  構成した分類器が ClassificationSpec を満たすこと                *)
(* ----------------------------------------------------------------- *)

Lemma strict_extension_above_or_below_sub : forall l sub r p,
  ClassificationContext l sub r ->
  ((l <> [] /\ onHead_extend_strict (l ++ sub ++ r) p)
   \/ (r <> [] /\ onLast_extend_strict (l ++ sub ++ r) p)) ->
  in_sub_x_range sub p ->
  above_sub_at_x sub p \/ below_sub_at_x sub p.
Proof.
  intros l sub r [xp yp] Hctx Hextend Hx.
  pose proof (context_sub_nonempty l sub r Hctx) as Hne.
  pose proof (context_sub_connected l sub r Hctx) as Hconn.
  pose proof (context_sub_x_monotone l sub r Hctx) as Hmono.
  pose proof (context_sparse l sub r Hctx) as Hsparse.
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
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    @ClassificationSpec l sub r (classify l sub r).
Proof.
  intros l sub r Hne Hmono Hsparse Hembed Hdisjoint.
  pose (Hctx := Build_ClassificationContext
                  l sub r Hne Hmono Hsparse Hembed Hdisjoint).
  assert (HwholeNe : l ++ sub ++ r <> []) by now apply whole_nonempty.
  constructor.
  - intros p Hp. unfold classify, constraint_classifier.
    destruct (excluded_middle_informative (onSegmentlist sub p));
      [reflexivity | contradiction].
  - intros seg Hseg. split; intros Hy.
    + eapply endpoint_order_classified; eauto.
      * exists seg. split; [exact Hseg | now left].
      * exists seg. split; [exact Hseg | now right].
      * apply rt_step. apply order_core_step.
        eapply order_on_segment with (seg := seg).
        -- exact Hseg.
        -- now left.
        -- now right.
        -- lra.
    + eapply endpoint_order_classified; eauto.
      * exists seg. split; [exact Hseg | now right].
      * exists seg. split; [exact Hseg | now left].
      * apply rt_step. apply order_core_step.
        eapply order_on_segment with (seg := seg).
        -- exact Hseg.
        -- now right.
        -- now left.
        -- lra.
  - intros i j s0 t ps pt Hs Ht Hij Hover Hps Hpt Hy.
    eapply endpoint_order_classified; eauto.
    + exists s0. split; [eapply nth_error_In; eauto | exact Hps].
    + exists t. split; [eapply nth_error_In; eauto | exact Hpt].
    + apply rt_step.
      apply order_core_step.
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
  - intros Hl p Hext Hrange.
    destruct (strict_extension_above_or_below_sub l sub r p Hctx
                (or_introl (conj Hl Hext)) Hrange) as [Habove | Hbelow].
    + left. apply (classify_forced_up l sub r _ Hctx).
      * now apply head_endpoint_of.
      * apply endpoint_seed_forced_up. split; [now apply head_endpoint_of |].
        right; left. split; [exact Hl |]. split; [reflexivity |].
        destruct Habove as [z [Hz [Hx Hy]]].
        exists p, z. repeat split; assumption.
    + right. apply (classify_forced_down l sub r _ Hctx).
      * now apply head_endpoint_of.
      * apply endpoint_seed_forced_down. split; [now apply head_endpoint_of |].
        right; left. split; [exact Hl |]. split; [reflexivity |].
        destruct Hbelow as [z [Hz [Hx Hy]]].
        exists p, z. repeat split; assumption.
  - intros Hr p Hext Hrange.
    destruct (strict_extension_above_or_below_sub l sub r p Hctx
                (or_intror (conj Hr Hext)) Hrange) as [Habove | Hbelow].
    + left. apply (classify_forced_up l sub r _ Hctx).
      * now apply last_endpoint_of.
      * apply endpoint_seed_forced_up. split; [now apply last_endpoint_of |].
        right; right. split; [exact Hr |]. split; [reflexivity |].
        destruct Habove as [z [Hz [Hx Hy]]].
        exists p, z. repeat split; assumption.
    + right. apply (classify_forced_down l sub r _ Hctx).
      * now apply last_endpoint_of.
      * apply endpoint_seed_forced_down. split; [now apply last_endpoint_of |].
        right; right. split; [exact Hr |]. split; [reflexivity |].
        destruct Hbelow as [z [Hz [Hx Hy]]].
        exists p, z. repeat split; assumption.
  - intros ph pl Hph Hpl Hx. split; intros Hy.
    + eapply endpoint_order_classified; eauto using head_endpoint_of, last_endpoint_of.
      apply rt_step. apply order_end_step.
      eapply order_head_last; eauto. lra.
    + eapply endpoint_order_classified; eauto using head_endpoint_of, last_endpoint_of.
      apply rt_step. apply order_end_step.
      eapply order_last_head; eauto. lra.
  - intros seg e q Hseg He Hq Hx. split; intros Hy; split.
    + eapply endpoint_order_classified; eauto using head_endpoint_of.
      * exists seg. split; [exact Hseg | now left].
      * apply rt_step. apply order_end_step.
        eapply order_head_below_segment; eauto; [lra | now left].
    + eapply endpoint_order_classified; eauto using head_endpoint_of.
      * exists seg. split; [exact Hseg | now right].
      * apply rt_step. apply order_end_step.
        eapply order_head_below_segment; eauto; [lra | now right].
    + eapply endpoint_order_classified; eauto using head_endpoint_of.
      * exists seg. split; [exact Hseg | now left].
      * apply rt_step. apply order_end_step.
        eapply order_segment_below_head; eauto; [lra | now left].
    + eapply endpoint_order_classified; eauto using head_endpoint_of.
      * exists seg. split; [exact Hseg | now right].
      * apply rt_step. apply order_end_step.
        eapply order_segment_below_head; eauto; [lra | now right].
  - intros seg e q Hseg He Hq Hx. split; intros Hy; split.
    + eapply endpoint_order_classified; eauto using last_endpoint_of.
      * exists seg. split; [exact Hseg | now left].
      * apply rt_step. apply order_end_step.
        eapply order_last_below_segment; eauto; [lra | now left].
    + eapply endpoint_order_classified; eauto using last_endpoint_of.
      * exists seg. split; [exact Hseg | now right].
      * apply rt_step. apply order_end_step.
        eapply order_last_below_segment; eauto; [lra | now right].
    + eapply endpoint_order_classified; eauto using last_endpoint_of.
      * exists seg. split; [exact Hseg | now left].
      * apply rt_step. apply order_end_step.
        eapply order_segment_below_last; eauto; [lra | now left].
    + eapply endpoint_order_classified; eauto using last_endpoint_of.
      * exists seg. split; [exact Hseg | now right].
      * apply rt_step. apply order_end_step.
        eapply order_segment_below_last; eauto; [lra | now right].
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
    endpoint_of sub p ->
    classify l sub r p = RegFix.
Proof.
  intros l sub r p Hend.
  unfold classify, constraint_classifier.
  destruct (excluded_middle_informative (onSegmentlist sub p));
    [reflexivity |].
  exfalso. apply n. now apply endpoint_of_onSegmentlist.
Qed.

Lemma operate_sub_endpoint :
  forall l sub r h p,
    endpoint_of sub p ->
    operate_point l sub r h p = p.
Proof.
  intros l sub r h p Hend.
  apply operate_point_RegFix.
  now apply classify_sub_endpoint.
Qed.
