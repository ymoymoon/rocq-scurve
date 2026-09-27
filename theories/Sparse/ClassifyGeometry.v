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

(* sub に隣接する左右のセグメントが、sub 側へ x 方向に戻る蓋か。 *)
Definition terminal_lid (l : list Segment) : Prop :=
  l <> [] /\
  fst (term (last_segment l)) < fst (init (last_segment l)).

Definition initial_lid (r : list Segment) : Prop :=
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

Lemma RegFix_at_or_above_not_up : forall g,
  g <> RegUp -> region_at_or_above RegFix g.
Proof.
  intros g Hnot. destruct g.
  - now left.
  - contradiction.
  - right. constructor.
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

(* 同じ x の二つの sub 点の間に p が入らない。sub 自身の点には要求しない。 *)
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

(* sub の全点は、全体の始点・終点という二つの出現を除き、
   その両端を対角線とする開長方形の内部にある。 *)
Definition sub_strictly_inside_endpoint_rect (sub : list Segment) : Prop :=
  forall i s p,
    nth_error sub i = Some s ->
    onSegment s p ->
    (i = 0%nat -> p <> init s) ->
    (S i = length sub -> p <> term s) ->
    in_rect (rect_of sub) p.

(* x 単調性の代わりに、構成時に選ぶ具体的な埋め込みへ要求する幾何条件。 *)
Record PreparedGeometry (l sub r : list Segment) : Prop := {
  prepared_sub_nonempty : sub <> [];
  prepared_sub_strictly_inside : sub_strictly_inside_endpoint_rect sub;
  prepared_sub_x_order :
    fst (init (hd_segment sub)) < fst (term (last_segment sub));
  prepared_external_no_gap : external_points_avoid_sub_vertical_gap l sub r;
  prepared_no_terminal_lid : ~ terminal_lid l;
  prepared_no_initial_lid : ~ initial_lid r
}.

(* 開内部条件は端点長方形への閉包含を含意する。二つの全体端点だけを別扱いする。 *)
Lemma prepared_sub_contained : forall l sub r,
  PreparedGeometry l sub r -> sub_contained_in_endpoint_rect sub.
Proof.
  intros l sub r Hgeometry p [s [Hin Hon]].
  destruct (In_nth_error sub s Hin) as [i Hnth].
  pose proof (prepared_sub_strictly_inside l sub r Hgeometry) as Hstrict.
  destruct (classic (p = init (hd_segment sub))) as [Hfirst | Hfirst].
  - subst p. unfold in_rect_or_endpoints_at, in_closed_rect, rect_of; simpl.
    split; split;
      pose proof (Rmin_l (fst (init (hd_segment sub)))
                          (fst (term (last_segment sub))));
      pose proof (Rmax_l (fst (init (hd_segment sub)))
                          (fst (term (last_segment sub))));
      pose proof (Rmin_l (snd (init (hd_segment sub)))
                          (snd (term (last_segment sub))));
      pose proof (Rmax_l (snd (init (hd_segment sub)))
                          (snd (term (last_segment sub)))); lra.
  - destruct (classic (p = term (last_segment sub))) as [Hlast | Hlast].
    + subst p. unfold in_rect_or_endpoints_at, in_closed_rect, rect_of; simpl.
      split; split;
        pose proof (Rmin_r (fst (init (hd_segment sub)))
                            (fst (term (last_segment sub))));
        pose proof (Rmax_r (fst (init (hd_segment sub)))
                            (fst (term (last_segment sub))));
        pose proof (Rmin_r (snd (init (hd_segment sub)))
                            (snd (term (last_segment sub))));
        pose proof (Rmax_r (snd (init (hd_segment sub)))
                            (snd (term (last_segment sub)))); lra.
    + assert (HnotFirst : i = 0%nat -> p <> init s).
      { intros Hi Hp. subst i. destruct sub as [|a tail]; [discriminate |].
        simpl in Hnth. inversion Hnth; subst s. apply Hfirst. exact Hp. }
      assert (HnotLast : S i = length sub -> p <> term s).
      { intros Hi Hp. apply Hlast. rewrite Hp.
        assert (Hidx : i = (length sub - 1)%nat) by lia.
        subst i.
        assert (HlastNth :
          nth_error sub (length sub - 1) = Some (last_segment sub)).
        { unfold last_segment. apply nth_error_last.
          exact (prepared_sub_nonempty l sub r Hgeometry). }
        rewrite Hnth in HlastNth. now inversion HlastNth. }
      pose proof (Hstrict i s p Hnth Hon HnotFirst HnotLast) as Hinside.
      unfold in_rect_or_endpoints_at, in_closed_rect.
      unfold in_rect in Hinside. destruct Hinside as [[Hx0 Hx1] [Hy0 Hy1]].
      split; split; lra.
Qed.

(* 最初以外の部分セグメントは、全体の左端 x に戻らない。 *)
Lemma prepared_inner_segment_left_x : forall l sub r k s,
  PreparedGeometry l sub r ->
  nth_error sub k = Some s ->
  (0 < k)%nat ->
  rx0 (rect_of sub) < rx0 (rect_of [s]).
Proof.
  intros l sub r k s Hgeometry Hnth Hk.
  pose proof (prepared_sub_strictly_inside l sub r Hgeometry) as Hstrict.
  pose proof (prepared_sub_x_order l sub r Hgeometry) as Horder.
  assert (Hne : sub <> []).
  { exact (prepared_sub_nonempty l sub r Hgeometry). }
  assert (Hdistinct : init s <> term s).
  { exact (neq_init_term s). }
  assert (Hinit : in_rect (rect_of sub) (init s)).
  { apply (Hstrict k s (init s) Hnth (onInit s)).
    - intro Hzero. exfalso. lia.
    - intros HlastEq. exact Hdistinct. }
  assert (HtermX : rx0 (rect_of sub) < fst (term s)).
  { destruct (Nat.eq_dec (S k) (length sub)) as [Hlast | Hnotlast].
    - assert (Hindex : k = (length sub - 1)%nat) by lia.
      subst k.
      assert (HlastNth :
          nth_error sub (length sub - 1) = Some (last_segment sub)).
      { unfold last_segment. now apply nth_error_last. }
      rewrite Hnth in HlastNth. inversion HlastNth; subst s.
      unfold rect_of. simpl.
      rewrite Rmin_left by lra. exact Horder.
    - pose proof (Hstrict k s (term s) Hnth (onTerm s)) as Hinside.
      assert (Hfirst : k = 0%nat -> term s <> init s).
      { intros Hzero Heq. apply Hdistinct. symmetry. exact Heq. }
      assert (Hlast' : S k = length sub -> term s <> term s).
      { intro Heq. exfalso. contradiction. }
      specialize (Hinside Hfirst Hlast').
      exact (proj1 (proj1 Hinside)). }
  unfold in_rect in Hinit. destruct Hinit as [[HinitX _] _].
  unfold rect_of at 2. simpl.
  apply Rmin_glb_lt; assumption.
Qed.

(* 最後以外の部分セグメントは、全体の右端 x に戻らない。 *)
Lemma prepared_inner_segment_right_x : forall l sub r k s,
  PreparedGeometry l sub r ->
  nth_error sub k = Some s ->
  (S k < length sub)%nat ->
  rx1 (rect_of [s]) < rx1 (rect_of sub).
Proof.
  intros l sub r k s Hgeometry Hnth Hk.
  pose proof (prepared_sub_strictly_inside l sub r Hgeometry) as Hstrict.
  pose proof (prepared_sub_x_order l sub r Hgeometry) as Horder.
  assert (Hdistinct : init s <> term s).
  { exact (neq_init_term s). }
  assert (Hterm : in_rect (rect_of sub) (term s)).
  { apply (Hstrict k s (term s) Hnth (onTerm s)).
    - intros Hzero Heq. apply Hdistinct. symmetry. exact Heq.
    - intro Hlast. exfalso. lia. }
  assert (HinitX : fst (init s) < rx1 (rect_of sub)).
  { destruct (Nat.eq_dec k 0) as [Hzero | Hnonzero].
    - subst k. destruct sub as [|first rest]; [discriminate |].
      simpl in Hnth. inversion Hnth; subst s.
      simpl in Horder. unfold rect_of. simpl.
      unfold Rmax. destruct Rle_dec; lra.
    - pose proof (Hstrict k s (init s) Hnth (onInit s)) as Hinside.
      assert (Hfirst : k = 0%nat -> init s <> init s).
      { intro Heq. exfalso. contradiction. }
      assert (Hlast' : S k = length sub -> init s <> term s).
      { intros HlastEq. exact Hdistinct. }
      specialize (Hinside Hfirst Hlast').
      exact (proj2 (proj1 Hinside)). }
  unfold in_rect in Hterm. destruct Hterm as [[_ HtermX] _].
  unfold rect_of at 1. simpl.
  apply Rmax_lub_lt; assumption.
Qed.

(* [p] と同じ x にある sub 上の全ての点より、[p] が厳密に上にある。
   全称形にしておくと、sub 上への到達時には [q := p] で直ちに矛盾する。 *)
Definition strictly_above_sub_at_x
    (sub : list Segment) (p : Point) : Prop :=
  forall q,
    onSegmentlist sub q ->
    fst p = fst q ->
    snd q < snd p.

Definition strictly_below_sub_at_x
    (sub : list Segment) (p : Point) : Prop :=
  forall q,
    onSegmentlist sub q ->
    fst p = fst q ->
    snd p < snd q.

(* 外部点では、存在形の上下判定は全ての同じ x の sub 点に通用する。 *)
Lemma no_gap_above_all : forall sub p,
  ~ onSegmentlist sub p ->
  avoids_sub_vertical_gap sub p ->
  above_sub_at_x sub p ->
  strictly_above_sub_at_x sub p.
Proof.
  intros sub p Houtside Hgap [qlo [Hlo [Hxlo Hylo]]] qhi Hhi Hxhi.
  destruct (total_order_T (snd qhi) (snd p)) as [[Hlt | Heq] | Hgt].
  - exact Hlt.
  - exfalso. apply Houtside.
    destruct p as [xp yp], qhi as [xq yq]; simpl in *.
    assert (xp = xq) by lra. assert (yp = yq) by lra. subst.
    exact Hhi.
  - exfalso. apply Hgap.
    exists qlo, qhi. repeat split; assumption.
Qed.

Lemma no_gap_below_all : forall sub p,
  ~ onSegmentlist sub p ->
  avoids_sub_vertical_gap sub p ->
  below_sub_at_x sub p ->
  strictly_below_sub_at_x sub p.
Proof.
  intros sub p Houtside Hgap [qhi [Hhi [Hxhi Hyhi]]] qlo Hlo Hxlo.
  destruct (total_order_T (snd p) (snd qlo)) as [[Hlt | Heq] | Hgt].
  - exact Hlt.
  - exfalso. apply Houtside.
    destruct p as [xp yp], qlo as [xq yq]; simpl in *.
    assert (xp = xq) by lra. assert (yp = yq) by lra. subst.
    exact Hlo.
  - exfalso. apply Hgap.
    exists qlo, qhi. repeat split; assumption.
Qed.

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
