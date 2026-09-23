Require Export Sparse.SparsePrelude.
Require Import Admissible.
Require Import Reduction.
Require Import Stdlib.Reals.Reals.
Require Import Embed.
Require Import PrimitiveSegment.
Require Import Segment.
Require Import SegmentsTranslation.
Require Import ListExt.
Require Import Stdlib.Logic.ClassicalDescription.
Require Import Stdlib.Reals.Rsqrt_def.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.

(* 連続な実数値関数が区間上で 0 を取らなければ、その符号は変わらない。 *)
Lemma continuous_nonzero_sign_constant :
  forall (f : R -> R) a b,
    continuity f ->
    (forall t, Rmin a b <= t <= Rmax a b -> f t <> 0) ->
    (f a < 0 -> f b < 0)
    /\ (0 < f a -> 0 < f b).
Proof.
  intros f a b Hcontinuous Hnonzero. split.
  - intros Ha.
    destruct (total_order_T (f b) 0) as [[Hb | Hb] | Hb];
      [exact Hb | exfalso | exfalso].
    + apply (Hnonzero b); [split; [apply Rmin_r | apply Rmax_r] | exact Hb].
    + destruct (total_order_T a b) as [[Hab | Hab] | Hab].
      * destruct (IVT f a b Hcontinuous Hab Ha Hb) as [z [Hz Hzero]].
        exact (Hnonzero z ltac:(rewrite Rmin_left, Rmax_right; lra) Hzero).
      * subst b. lra.
      * assert (Hopp : continuity (- f)) by now apply continuity_opp.
        assert (Hnb : opp_fct f b < 0) by (unfold opp_fct; lra).
        assert (Hna : 0 < opp_fct f a) by (unfold opp_fct; lra).
        destruct (IVT (opp_fct f) b a Hopp Hab Hnb Hna)
          as [z [Hz Hzero]].
        apply (Hnonzero z ltac:(rewrite Rmin_right, Rmax_left; lra)).
        unfold opp_fct in Hzero. lra.
  - intros Ha.
    destruct (total_order_T 0 (f b)) as [[Hb | Hb] | Hb];
      [exact Hb | exfalso | exfalso].
    + apply (Hnonzero b); [split; [apply Rmin_r | apply Rmax_r] | lra].
    + destruct (total_order_T a b) as [[Hab | Hab] | Hab].
      * assert (Hopp : continuity (- f)) by now apply continuity_opp.
        assert (Hna : opp_fct f a < 0) by (unfold opp_fct; lra).
        assert (Hnb : 0 < opp_fct f b) by (unfold opp_fct; lra).
        destruct (IVT (opp_fct f) a b Hopp Hab Hna Hnb)
          as [z [Hz Hzero]].
        apply (Hnonzero z ltac:(rewrite Rmin_left, Rmax_right; lra)).
        unfold opp_fct in Hzero. lra.
      * subst b. lra.
      * destruct (IVT f b a Hcontinuous Hab Hb Ha) as [z [Hz Hzero]].
        exact (Hnonzero z ltac:(rewrite Rmin_right, Rmax_left; lra) Hzero).
Qed.

(* 連続曲線と連続な高さ関数が交わらなければ、曲線の上下側は変わらない。
   曲線を x の関数と仮定しないため、垂直な部分にも適用できる。 *)
Lemma continuous_curve_vertical_order_constant :
  forall (curve : R -> Point) (height : R -> R) a b,
    continuity (fun t => fst (curve t)) ->
    continuity (fun t => snd (curve t)) ->
    continuity height ->
    (forall t,
      Rmin a b <= t <= Rmax a b ->
      snd (curve t) <> height (fst (curve t))) ->
    (height (fst (curve a)) < snd (curve a) ->
       height (fst (curve b)) < snd (curve b))
    /\
    (snd (curve a) < height (fst (curve a)) ->
       snd (curve b) < height (fst (curve b))).
Proof.
  intros curve height a b Hx Hy Hheight Hdisjoint.
  set (gap := fun t => snd (curve t) - height (fst (curve t))).
  assert (HgapContinuous : continuity gap).
  { unfold gap.
    change (continuity
      ((fun t => snd (curve t)) -
       (comp height (fun t => fst (curve t))))).
    apply continuity_minus; [exact Hy |].
    now apply continuity_comp. }
  assert (HgapNonzero : forall t,
      Rmin a b <= t <= Rmax a b -> gap t <> 0).
  { intros t Ht Hzero. apply (Hdisjoint t Ht).
    unfold gap in Hzero. lra. }
  destruct (continuous_nonzero_sign_constant
              gap a b HgapContinuous HgapNonzero) as [Hnegative Hpositive].
  split; intros Horder.
  - specialize (Hpositive ltac:(unfold gap; lra)).
    unfold gap in Hpositive. lra.
  - specialize (Hnegative ltac:(unfold gap; lra)).
    unfold gap in Hnegative. lra.
Qed.

(* セグメントと延長線の任意の部分曲線は、端点の x 範囲を飛び出さない。
   本体では x 単調性から従い、延長部分についても同じ幾何仕様を要求する。 *)
Axiom segment_x_between_parameters : forall seg t0 t1 t,
  t0 <= t <= t1 ->
  Rmin (fst (point seg t0)) (fst (point seg t1)) <= fst (point seg t)
  <= Rmax (fst (point seg t0)) (fst (point seg t1)).



(* 基本プリミティブ。 *)

Definition rightabove (rr1 rr2 : Point) :=
  let (x1, y1) := rr1 in
  let (x2, y2) := rr2 in x1 < x2 /\ y1 < y2.
Definition rightbelow (rr1 rr2 : Point) :=
  let (x1, y1) := rr1 in
  let (x2, y2) := rr2 in x1 < x2 /\ y2 < y1.

Definition connected (ls : list Segment) : Prop :=
  forall i s1 s2, nth_error ls i = Some s1 -> nth_error ls (S i) = Some s2 ->
    term s1 = init s2.

(* 連結な列の連続部分列は連結である。 *)
Lemma connected_middle :
  forall l sub r,
    connected (l ++ sub ++ r) -> connected sub.
Proof.
  intros l sub r Hconn i s1 s2 H1 H2.
  apply (Hconn (length l + i)%nat s1 s2).
  - change (nth_error (l ++ (sub ++ r)) (length l + i) = Some s1).
    assert (Hle : (length l <= length l + i)%nat) by lia.
    rewrite (nth_error_app2 l (sub ++ r) Hle).
    replace (length l + i - length l)%nat with i by lia.
    rewrite nth_error_app1; [exact H1 |].
    apply nth_error_Some. rewrite H1. discriminate.
  - replace (S (length l + i)) with (length l + S i)%nat by lia.
    change (nth_error (l ++ (sub ++ r)) (length l + S i) = Some s2).
    assert (Hle : (length l <= length l + S i)%nat) by lia.
    rewrite (nth_error_app2 l (sub ++ r) Hle).
    replace (length l + S i - length l)%nat with (S i) by lia.
    rewrite nth_error_app1; [exact H2 |].
    apply nth_error_Some. rewrite H2. discriminate.
Qed.

Lemma connected_app_junction :
  forall l r,
    connected (l ++ r) ->
    l <> [] ->
    r <> [] ->
    term (last_segment l) = init (hd_segment r).
Proof.
  intros [|a l] r Hconn Hl Hr; [contradiction |].
  apply (Hconn (length l) (last_segment (a :: l)) (hd_segment r)).
  - rewrite nth_error_app1 by (simpl; lia).
    replace (length l) with (length (a :: l) - 1)%nat by (simpl; lia).
    apply nth_error_last. discriminate.
  - replace (S (length l)) with (length (a :: l)) by reflexivity.
    rewrite nth_error_app2 by lia.
    replace (length (a :: l) - length (a :: l))%nat with 0%nat by lia.
    destruct r; [contradiction | reflexivity].
Qed.

Definition onSegment' (seg: Segment) (rr : R * R) := exists (t:R), 0 < t <= 1 /\ point seg t = rr.
(* TODO: 空リストを省く *)
Definition onSegmentlist l rr := exists seg, In seg l /\ onSegment seg rr.

(* セグメント本体と両側の延長を、同じ連続 trace として扱う。 *)
Inductive SegmentTracePart : Type :=
  | TraceBody
  | TraceHead
  | TraceLast.

Definition onSegmentTrace
    (part : SegmentTracePart) (seg : Segment) (p : Point) : Prop :=
  match part with
  | TraceBody => onSegment seg p
  | TraceHead => onHead seg p
  | TraceLast => onLast seg p
  end.

Definition trace_parameter_range (part : SegmentTracePart) (t : R) : Prop :=
  match part with
  | TraceBody => 0 <= t <= 1
  | TraceHead => t <= 0
  | TraceLast => 1 <= t
  end.

Lemma onSegmentTrace_parameter : forall part seg p,
  onSegmentTrace part seg p ->
  exists t, trace_parameter_range part t /\ point seg t = p.
Proof.
  intros [] seg p H; exact H.
Qed.

Lemma trace_parameter_range_between : forall part t0 t1 t,
  trace_parameter_range part t0 ->
  trace_parameter_range part t1 ->
  Rmin t0 t1 <= t <= Rmax t0 t1 ->
  trace_parameter_range part t.
Proof.
  intros [] t0 t1 t Ht0 Ht1 Hbetween; cbn in *;
    unfold Rmin, Rmax in Hbetween; repeat destruct Rle_dec; lra.
Qed.

Lemma point_onSegmentTrace : forall part seg t,
  trace_parameter_range part t ->
  onSegmentTrace part seg (point seg t).
Proof.
  intros [] seg t Ht; cbn in *; exists t; now split.
Qed.

Definition trace_disjoint_from_segmentlist
    (part : SegmentTracePart) (seg : Segment) (ls : list Segment) : Prop :=
  forall p, onSegmentTrace part seg p -> ~ onSegmentlist ls p.

(* 連結な x 単調セグメント列を、その x 座標における高さ関数として取る。
   区間外では任意の連続延長を許し、以下では列上の x だけを使用する。 *)
Parameter segmentlist_height : list Segment -> R -> R.

Axiom connected_x_monotone_height_on_between :
  forall sub p q x,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    onSegmentlist sub q ->
    Rmin (fst p) (fst q) <= x <= Rmax (fst p) (fst q) ->
    onSegmentlist sub (x, segmentlist_height sub x).

Axiom connected_x_monotone_height_unique :
  forall sub p q,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    onSegmentlist sub q ->
    fst p = fst q ->
    snd p = snd q.

Axiom connected_x_monotone_height_continuous :
  forall sub,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    continuity (segmentlist_height sub).

(* 連続な非交差 trace と連結な x 単調 sub の上下関係は反転しない。
   一般の連続曲線に対する符号保存へ還元するため、垂直部分も許される。 *)
Lemma disjoint_trace_sub_vertical_order_constant :
  forall part seg sub,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    trace_disjoint_from_segmentlist part seg sub ->
    forall p0 q0 p q,
      onSegmentTrace part seg p0 ->
      onSegmentlist sub q0 ->
      fst p0 = fst q0 ->
      onSegmentTrace part seg p ->
      onSegmentlist sub q ->
      fst p = fst q ->
      (snd q0 < snd p0 -> snd q < snd p)
      /\ (snd p0 < snd q0 -> snd p < snd q).
Proof.
  intros part seg sub Hsub Hconnected Hmonotone Hdisjoint
    p0 q0 p q Hp0 Hq0 Hx0 Hp Hq Hx.
  destruct (onSegmentTrace_parameter part seg p0 Hp0)
    as [t0 [Ht0 Hp0eq]].
  destruct (onSegmentTrace_parameter part seg p Hp)
    as [t [Ht Hpeq]].
  subst p0; subst p.
  assert (HtraceBetween : forall u,
      Rmin t0 t <= u <= Rmax t0 t ->
      onSegmentTrace part seg (point seg u)).
  { intros u Hu. apply point_onSegmentTrace.
    exact (trace_parameter_range_between part t0 t u Ht0 Ht Hu). }
  assert (HverticalDisjoint : forall u,
      Rmin t0 t <= u <= Rmax t0 t ->
      snd (point seg u) <> segmentlist_height sub (fst (point seg u))).
  {
    intros u Hu Hequal.
    assert (Hxu :
        Rmin (fst q0) (fst q) <= fst (point seg u)
        <= Rmax (fst q0) (fst q)).
    { destruct (Rle_dec t0 t) as [Horder | Horder].
      - assert (Ht0ut : t0 <= u <= t) by
          (rewrite Rmin_left, Rmax_right in Hu; assumption).
        pose proof
          (segment_x_between_parameters seg t0 t u Ht0ut) as Hbetween.
        rewrite Hx0, Hx in Hbetween. exact Hbetween.
      - assert (Htt0 : t <= t0) by lra.
        assert (Htut0 : t <= u <= t0) by
          (rewrite Rmin_right, Rmax_left in Hu; lra).
        pose proof
          (segment_x_between_parameters seg t t0 u Htut0) as Hbetween.
        rewrite Hx0, Hx in Hbetween.
        rewrite Rmin_comm, Rmax_comm in Hbetween.
        exact Hbetween. }
    pose proof (connected_x_monotone_height_on_between
                  sub q0 q (fst (point seg u))
                  Hsub Hconnected Hmonotone Hq0 Hq Hxu) as HheightOn.
    apply (Hdisjoint (point seg u)).
    - now apply HtraceBetween.
    - replace (point seg u)
        with (fst (point seg u), segmentlist_height sub (fst (point seg u))).
      + exact HheightOn.
      + apply injective_projections; [reflexivity |].
        cbn. exact (eq_sym Hequal).
  }
  assert (Hheight0 :
      segmentlist_height sub (fst q0) = snd q0).
  {
    assert (Hon : onSegmentlist sub
        (fst q0, segmentlist_height sub (fst q0))).
    { apply (connected_x_monotone_height_on_between sub q0 q0 (fst q0));
        try assumption.
      unfold Rmin, Rmax. repeat destruct Rle_dec; lra. }
    pose proof (connected_x_monotone_height_unique
                  sub (fst q0, segmentlist_height sub (fst q0)) q0
                  Hsub Hconnected Hmonotone Hon Hq0 eq_refl) as Heq.
    cbn in Heq. exact Heq.
  }
  assert (Hheight :
      segmentlist_height sub (fst q) = snd q).
  {
    assert (Hon : onSegmentlist sub
        (fst q, segmentlist_height sub (fst q))).
    { apply (connected_x_monotone_height_on_between sub q q (fst q));
        try assumption.
      unfold Rmin, Rmax. repeat destruct Rle_dec; lra. }
    pose proof (connected_x_monotone_height_unique
                  sub (fst q, segmentlist_height sub (fst q)) q
                  Hsub Hconnected Hmonotone Hon Hq eq_refl) as Heq.
    cbn in Heq. exact Heq.
  }
  destruct (continuous_curve_vertical_order_constant
              (point seg) (segmentlist_height sub) t0 t
              (proj1 (seg_continuous seg))
              (proj2 (seg_continuous seg))
              (connected_x_monotone_height_continuous
                 sub Hsub Hconnected Hmonotone)
              HverticalDisjoint) as [Habove Hbelow].
  split; intros Horder.
  - cbn in Habove. rewrite Hx0, Hheight0, Hx, Hheight in Habove.
    now apply Habove.
  - cbn in Hbelow. rewrite Hx0, Hheight0, Hx, Hheight in Hbelow.
    now apply Hbelow.
Qed.

(* TODO: extend に関する公理を完成させた後， onExtendSegment と整合することを確認
		特に空リストの扱い *)
Definition onExtend ls rr := exists t, rr = extend ls t.

(* リスト補助（hd / last と map の交換．空リスト回避のため非空を仮定）*)
Lemma hd_map_nonnil :
  forall (f : Segment -> Segment) ls,
    ls <> [] -> hd_segment (map f ls) = f (hd_segment ls).
Proof.
  intros f ls H. destruct ls as [|a tl]; [contradiction | reflexivity].
Qed.

Lemma last_map_nonnil :
  forall (f : Segment -> Segment) ls,
    ls <> [] -> last_segment (map f ls) = f (last_segment ls).
Proof.
  intros f [|a tl] H; [contradiction|].
  clear H. unfold last_segment. revert a.
  induction tl as [|b tl IH]; intros a; simpl; [reflexivity|].
  exact (IH b).
Qed.

Lemma last_app_nonnil :
  forall (xs ys : list Segment),
    ys <> [] -> last_segment (xs ++ ys) = last_segment ys.
Proof.
  unfold last_segment. induction xs as [|a xs IH]; intros ys H; simpl; [reflexivity|].
  destruct (xs ++ ys) eqn:E.
  - destruct xs; destruct ys; simpl in E; try discriminate; contradiction.
  - rewrite <- E. apply IH; exact H.
Qed.

Lemma last_In :
  forall (ls : list Segment),
    ls <> [] -> In (last_segment ls) ls.
Proof.
  intros ls H.
  apply exists_last in H.
  destruct H as [l' [b H]].
  rewrite H.
  unfold last_segment.
  rewrite last_last.
  apply in_or_app.
  right.
  constructor.
  reflexivity.
Qed.

Lemma nth_error_map_inv :
  forall (f : Segment -> Segment) ls n s,
    nth_error (map f ls) n = Some s ->
    exists s0, nth_error ls n = Some s0 /\ s = f s0.
Proof.
  intros f ls n s H. rewrite nth_error_map in H.
  destruct (nth_error ls n) as [s0|] eqn:E; simpl in H; [|discriminate].
  injection H as H. exists s0. split; [reflexivity | now symmetry].
Qed.

Lemma nth_error_lt : forall (ls : list Segment) i s,
  nth_error ls i = Some s -> (i < length ls)%nat.
Proof. intros ls i s H. apply nth_error_Some. rewrite H. discriminate. Qed.

Lemma nth_error_nth_eq : forall (ls : list Segment) i s d,
  nth_error ls i = Some s -> nth i ls d = s.
Proof.
  induction ls as [|a tl IH]; intros i s d H.
  - destruct i; simpl in H; discriminate.
  - destruct i as [|i]; simpl in H; simpl.
    + injection H as H; now subst.
    + now apply IH.
Qed.

(* 同じ長さの接頭辞を持つ二つの連結表示は、それぞれの部分が一致する。 *)
Lemma app_split_eq : forall (A : Type) (l1 l2 m1 m2 : list A),
  l1 ++ l2 = m1 ++ m2 -> length l1 = length m1 -> l1 = m1 /\ l2 = m2.
Proof.
  intros A. induction l1 as [|a l1 IH]; intros l2 m1 m2 H HL.
  - destruct m1 as [|b m1]; simpl in *; [split; [reflexivity | exact H] | discriminate].
  - destruct m1 as [|b m1]; simpl in *; [discriminate|].
    injection H as Hab H. injection HL as HL.
    destruct (IH _ _ _ H HL) as [E1 E2].
    split; [f_equal; assumption | exact E2].
Qed.

(* onSegmentlist に関する補題 *)
Lemma onSegmentlist_init_hd :
  forall sub, sub <> [] -> onSegmentlist sub (init (hd_segment sub)).
Proof.
  intros sub H. destruct sub as [|a tl]; [contradiction|].
  exists a. split; [left; reflexivity|]. exists 0. split; [lra | reflexivity].
Qed.

Lemma onSegmentlist_term_last :
  forall sub, sub <> [] -> onSegmentlist sub (term (last_segment sub)).
Proof.
  intros sub H. exists (last_segment sub). split.
  - apply last_In. assumption.
  - exists 1. split; [lra | reflexivity].
Qed.

(* ---- 位置 -------------------------------------------------------- *)

Definition at_pos (ls : list Segment) (q : Pos) : Point :=
  point (nth (fst q) ls default_segment) (snd q).

Definition onExtAt (ls : list Segment) (i : nat) (p : Point) : Prop :=
  exists t, in_range ls (i, t) /\ at_pos ls (i, t) = p.

(* 隣接セグメントの共有端点（自己交差ではない）*)
Definition junction (ls : list Segment) (q1 q2 : Pos) : Prop :=
  (S (fst q1) = fst q2 /\ snd q1 = 1 /\ snd q2 = 0)
  \/ (S (fst q2) = fst q1 /\ snd q2 = 1 /\ snd q1 = 0).

Definition crossing (ls : list Segment) : Prop :=
  exists q1 q2, in_range ls q1 /\ in_range ls q2
             /\ at_pos ls q1 = at_pos ls q2
             /\ q1 <> q2.

(* in_range な2位置は決して junction をなさない *)
Lemma no_junction : forall ls q1 q2,
  in_range ls q1 -> in_range ls q2 -> ~ junction ls q1 q2.
Proof.
  intros ls q1 q2 [_ [H1 _]] [_ [H2 _]] [(Hs & Ha & Hb) | (Hs & Ha & Hb)].
  - destruct H2 as [H2|H2]; [rewrite H2 in Hs; discriminate | lra].
  - destruct H1 as [H1|H1]; [rewrite H1 in Hs; discriminate | lra].
Qed.

(* extend ls t は位置 pos_of ls t の点である *)
Lemma extend_at_pos : forall ls t,
  ls <> [] -> extend ls t = at_pos ls (pos_of ls t).
Proof.
  intros ls t Hne.
  destruct (extend_repr ls t Hne) as [s [Hnth Heq]].
  unfold at_pos, pos_of; simpl.
  rewrite (nth_error_nth_eq ls (extend_index ls t) s default_segment Hnth).
  exact Heq.
Qed.

(* その位置は in_range に入る（3つの領域すべてで確認）*)
Lemma pos_of_in_range : forall ls t, ls <> [] -> in_range ls (pos_of ls t).
Proof.
  intros ls t Hne.
  destruct (extend_repr ls t Hne) as [s [Hnth _]].
  unfold in_range, pos_of; simpl.
  split; [ eapply nth_error_lt; exact Hnth |].
  destruct (extend_param_region ls t Hne) as [Hmid | [[Hi Hle] | [Hi Hgt]]].
  - (* 0 < param <= 1 : 本体 *)      split; [right; lra | right; lra].
  - (* index = 0, param <= 0 : 先頭延長 *) split; [left; exact Hi | right; lra].
  - (* 末尾, 1 < param : 末尾延長 *)  split; [right; lra | left; exact Hi].
Qed.

(* ---- close との橋渡し（既存の close の定義に依存する唯一の箇所）--- *)
Lemma close_crossing : forall ls, ls <> [] -> close ls -> crossing ls.
Proof.
  intros ls Hne Hcl.
  unfold close, close_extended in Hcl.
  destruct Hcl as [t1 [t2 [Hne12 Heq]]].

  (* ★ rewrite は仮説側で行う（ゴールの形に依存しない） *)
  rewrite (extend_at_pos ls t1 Hne), (extend_at_pos ls t2 Hne) in Heq.

  assert (Hr1 : in_range ls (pos_of ls t1)) by (apply pos_of_in_range; exact Hne).
  assert (Hr2 : in_range ls (pos_of ls t2)) by (apply pos_of_in_range; exact Hne).
  assert (Hq : pos_of ls t1 <> pos_of ls t2).
  { intros Hq. apply Hne12.
    eapply extend_same_piece_injective; [exact Hne | |].
    - change (fst (pos_of ls t1) = fst (pos_of ls t2)). rewrite Hq; reflexivity.
    - change (snd (pos_of ls t1) = snd (pos_of ls t2)). rewrite Hq; reflexivity. }

  exists (pos_of ls t1), (pos_of ls t2).
  split; [exact Hr1 |].
  split; [exact Hr2 |].
  split; [exact Heq | exact Hq].
Qed.

Lemma crossing_close : forall ls, ls <> [] -> crossing ls -> close ls.
Proof.
  intros ls Hne (q1 & q2 & Hr1 & Hr2 & Hpt & Hq).
  destruct (extend_onto ls q1 Hne Hr1) as [t1 Ht1].
  destruct (extend_onto ls q2 Hne Hr2) as [t2 Ht2].
  unfold close, close_extended. exists t1, t2. split.
  - intros Ht. apply Hq. rewrite <- Ht1, <- Ht2, Ht. reflexivity.
  - rewrite (extend_at_pos ls t1 Hne), (extend_at_pos ls t2 Hne), Ht1, Ht2.
    exact Hpt.
Qed.

Corollary open_no_crossing : forall ls, ls <> [] -> ~ close ls -> ~ crossing ls.
Proof. intros ls Hne H Hc. apply H. apply crossing_close; assumption. Qed.


(* embed_scurve, listDir に関わる補題 *)
Definition nil_scurve : scurve := exist _ nil IsScurveNil.

Lemma proj1_nil_scurve : proj1_sig nil_scurve = nil.
Proof. reflexivity. Qed.

(* connect の定義（exist _ (ps :: proj1_sig lp) _）から定義的に成立 *)
Lemma proj1_connect : forall ps lp A,
  proj1_sig (connect ps lp A) = ps :: proj1_sig lp.
Proof. intros. reflexivity. Qed.

(* dc_pseg_hd は「相手リストの先頭だけ」を見る（DcNil / DcCons の形から）*)
Lemma dc_pseg_hd_hd_error : forall ps l1 l2,
  hd_error l1 = hd_error l2 -> dc_pseg_hd ps l1 -> dc_pseg_hd ps l2.
Proof.
  intros ps l1 l2 Hhd H. 
  destruct l1, l2; simpl in Hhd; inversion Hhd.
  - assumption.
  - subst.
    constructor.
    inversion H.
    assumption.
Qed.

(* scurve_to_direction = map f ∘ proj1_sig であることの帰結2本 *)
Lemma std_length : forall sc,
  length (scurve_to_direction sc) = length (proj1_sig sc).
Proof.
  intros.
  unfold scurve_to_direction; apply length_map.
Qed.

Lemma std_app_of_proj : forall sc sc1 sc2,
  proj1_sig sc = proj1_sig sc1 ++ proj1_sig sc2 ->
  scurve_to_direction sc = scurve_to_direction sc1 ++ scurve_to_direction sc2.
Proof.
  intros.
  unfold scurve_to_direction; intros; rewrite H; apply map_app.
Qed.

Lemma embed_scurve_length : forall sc ls,
  embed_scurve sc ls -> length (proj1_sig sc) = length ls.
Proof.
  intros sc ls H. induction H as
    [ | ps s He | ps lp A s1 s2 ls' He Hsub IH Hcon ].
  - reflexivity.
  - rewrite proj1_connect. fold nil_scurve; rewrite proj1_nil_scurve. reflexivity.
  - rewrite proj1_connect. simpl. f_equal. exact IH.
Qed.

(* scurve の埋め込みを任意の位置で、向き列とセグメント列を揃えて分割する。 *)
Lemma embed_scurve_split : forall n sc ls,
  embed_scurve sc ls ->
  exists sc1 sc2 l1 l2,
       ls = l1 ++ l2
    /\ proj1_sig sc = proj1_sig sc1 ++ proj1_sig sc2
    /\ length (proj1_sig sc1) = Nat.min n (length (proj1_sig sc))
    /\ embed_scurve sc1 l1
    /\ embed_scurve sc2 l2.
Proof.
  induction n as [|n' IH]; intros sc ls H.

  (* ---- n = 0 : 何も取らない ---- *)
  - exists nil_scurve, sc, nil, ls.
    split; [reflexivity |].
    split; [reflexivity |].
    split; [reflexivity |].
    split; [exact EmbedScurveNil | exact H].

  (* ---- n = S n' ---- *)
  - destruct H as
      [ | ps s He | ps lp A s1 s2 ls' He Hsub Hcon ].

    (* 空曲線 *)
    + exists nil_scurve, nil_scurve, nil, nil.
      split; [reflexivity |].
      split; [reflexivity |].
      split; simpl; auto.
      split; exact EmbedScurveNil.

    (* 1本だけ：全部取る *)
    + exists (connect ps nil_scurve (DcNil ps)), nil_scurve, (s :: nil), nil.
      split; [reflexivity |].
      split; [rewrite proj1_connect, proj1_nil_scurve; reflexivity |].
      split.
      { rewrite proj1_connect, proj1_nil_scurve. simpl.
        rewrite Nat.min_r; [reflexivity | lia]. }
      split; [exact (EmbedScurveSigle ps s He) | exact EmbedScurveNil].

    (* 2本以上：先頭 ps を1つ取り、残りを IH で分割 *)
    + destruct (IH lp (s2 :: ls') Hsub)
        as (sc1' & sc2' & l1' & l2' & Els & Eps & Elen & Hc1 & Hc2).
      destruct (proj1_sig sc1') as [|q rest] eqn:Eq.

      (* (a) IH 側の前半が空 ⇒ 取るのは s1 だけ *)
      * assert (Hl1 : (length l1' = 0)%nat).
        { rewrite <- (embed_scurve_length _ _ Hc1), Eq. reflexivity. }
        destruct l1' as [|w tl]; simpl in Hl1; [| discriminate].
        simpl in Els. subst l2'.
        exists (connect ps nil_scurve (DcNil ps)), lp, (s1 :: nil), (s2 :: ls').
        split; [reflexivity |].
        split; [rewrite !proj1_connect, proj1_nil_scurve; reflexivity |].
        split.
        { rewrite !proj1_connect, proj1_nil_scurve. simpl.
          rewrite <- Elen. reflexivity. }
        split; [exact (EmbedScurveSigle ps s1 He) | exact Hsub].

      (* (b) IH 側の前半が非空 ⇒ ps を前に付け足す *)
      * assert (Hl1 : length l1' = S (length rest)).
        { rewrite <- (embed_scurve_length _ _ Hc1), Eq. reflexivity. }
        destruct l1' as [|w tl]; simpl in Hl1; [discriminate |].
        injection Els as Ew Els'. subst w.

        assert (Hhd : hd_error (proj1_sig lp) = hd_error (proj1_sig sc1')).
        { rewrite Eps, Eq. reflexivity. }
        assert (A' : dc_pseg_hd ps (proj1_sig sc1'))
          by (eapply dc_pseg_hd_hd_error; [exact Hhd | exact A]).

        exists (connect ps sc1' A'), sc2', (s1 :: s2 :: tl), l2'.
        split; [simpl; f_equal; f_equal; exact Els' |].
        split; [rewrite !proj1_connect, Eps, app_comm_cons; congruence|].
        split.
        { rewrite !proj1_connect. simpl. rewrite Eq, Elen. reflexivity. }
        split.
        { exact (EmbedScurveCons ps sc1' A' s1 s2 tl He Hc1 Hcon). }
        { exact Hc2. }
Qed.

(* ---- embed の分解 --------------------- *)
Lemma embed_split2 : forall ds1 ds2 ls,
  embed_listDir (ds1 ++ ds2) ls ->
  exists l1 l2, ls = l1 ++ l2 /\ embed_listDir ds1 l1 /\ embed_listDir ds2 l2.
Proof.
  intros ds1 ds2 ls [sc [Hdir Hemb]].
  destruct (embed_scurve_split (length ds1) sc ls Hemb)
    as (sc1 & sc2 & l1 & l2 & Els & Eps & Elen & H1 & H2).

  assert (Hd : scurve_to_direction sc
               = scurve_to_direction sc1 ++ scurve_to_direction sc2)
    by (apply std_app_of_proj; exact Eps).

  assert (Htot : (length (proj1_sig sc) = length ds1 + length ds2)%nat).
  { rewrite <- std_length, Hdir, length_app. reflexivity. }

  assert (Elen1 : length (scurve_to_direction sc1) = length ds1).
  { rewrite std_length, Elen, Htot. apply Nat.min_l, Nat.le_add_r. }

  rewrite Hdir in Hd.
  destruct (app_split_eq _ ds1 ds2 _ _ Hd (eq_sym Elen1)) as [E1 E2].

  exists l1, l2.
  split; [exact Els |].
  split.
  - exists sc1. split; [symmetry; exact E1 | exact H1].
  - exists sc2. split; [symmetry; exact E2 | exact H2].
Qed.

Lemma embed_split :
  forall ds1 sub_ds ds2 ls,
    embed_listDir (ds1 ++ sub_ds ++ ds2) ls ->
    exists l sub r,
      ls = l ++ sub ++ r
      /\ embed_listDir ds1 l /\ embed_listDir sub_ds sub /\ embed_listDir ds2 r.
Proof.
  intros ds1 sub_ds ds2 ls H.
  destruct (embed_split2 ds1 (sub_ds ++ ds2) ls H) as (l & m & Elm & Hl & Hm).
  destruct (embed_split2 sub_ds ds2 m Hm) as (sub & r & Em & Hsub & Hr).
  exists l, sub, r.
  split; [rewrite Elm, Em; reflexivity |].
  split; [exact Hl |].
  split; [exact Hsub | exact Hr].
Qed.


(* scurve の向き列と PrimitiveSegment 列の長さは一致する。 *)
Lemma scurve_listDir_length_consis: forall ds sc,
  scurve_to_direction sc = ds -> length ds = length (proj1_sig sc).
Proof.
	intros ds. unfold scurve_to_direction. 
	induction ds as [ | d ds' IH];  intros sc H.
	- (* ds = [] *) 
		destruct (proj1_sig sc); [auto | discriminate].
	- (* ds = d::ds' *) 
		destruct sc as [sc' Hsc].
		destruct Hsc as [ | p ps Hps H0]; try discriminate.
		simpl; f_equal.
		apply (IH (exist _ _ Hps)).
		simpl in *.
		injection H; auto.
Qed.

(* 向き列の長さとセグメント列の長さは一致する *)
Lemma embedding_listDir_length_consis: forall (ds: list Direction) (ls: list Segment),
  embed_listDir ds ls -> length ds = length ls.
Proof.
	intros ds ls [sc [Hdir Hembed]].
	rewrite (scurve_listDir_length_consis _ _ Hdir).
	apply scurve_length_consis.
	auto.
Qed.

Lemma embed_nonnil :
  forall ds ls, embed_listDir ds ls -> ds <> [] -> ls <> [].
Proof.
  intros ds ls Hembed Hds Hls.
  apply embedding_listDir_length_consis in Hembed.
  apply Hds.
  subst.
  apply length_zero_iff_nil.
  auto. 
Qed.

(* 単方向な向き列は空でない（is_one_way_scurve の定義から）*)
Lemma one_way_listDir_nonnil :
  forall ds, is_one_way_listDir ds -> ds <> [].
Proof.
  intros ds H contra.
  destruct H as [sc [Hdir Honeway]].
  destruct Honeway as [Hnonnil _].
  apply Hnonnil.
  subst.
  apply scurve_listDir_length_consis in contra.
  apply length_zero_iff_nil.
  auto.
Qed.

(*  (orn_seg としての)向き列が同じで、長さが同じで、連結なら、同じ ds の埋め込み」 *)
Lemma embed_scurve_transfer : forall ds ls ls',
  embed_listDir ds ls ->
  length ls' = length ls ->
  (forall i s s', nth_error ls i = Some s -> nth_error ls' i = Some s' ->
                  orn_seg s' = orn_seg s) ->
  connected ls' ->
  embed_listDir ds ls'.
Admitted.

(* ---- 連結性は埋め込みから出る（Embed.v の consist_init_term）---- *)
Lemma embed_scurve_connected : forall sc ls,
  embed_scurve sc ls -> connected ls.
Proof.
  intros sc ls Hembed.
  induction Hembed as [
    | ps s Hembed_ps
    | ps lp A s1 s2 ls Hembed_ps Hembed_tail Hterm IH].
  - unfold connected. intros i s1 s2 H1 H2.
    rewrite nth_error_nil in H1. discriminate H1.
  - unfold connected. intros i s1 s2 H1 H2.
    destruct i; simpl in H2; discriminate H2.
  - unfold connected in IH |- *. intros i x y Hx Hy.
    destruct i as [|i].
    + simpl in Hx, Hy. inversion Hx; inversion Hy; subst. exact IH.
    + simpl in Hx, Hy. now apply (Hterm i x y Hx Hy).
Qed.

Lemma embed_listDir_connected : forall ds ls, embed_listDir ds ls -> connected ls.
Proof.
  intros ds ls [sc [_ Hembed]].
  now apply (embed_scurve_connected sc ls).
Qed.


Definition horizontal_order (h : H) (x1 x2 : R) : Prop :=
  match h with
  | e => x1 <= x2
  | w => x2 <= x1
  end.

Definition vertical_order (v : V) (y1 y2 : R) : Prop :=
  match v with
  | n => y1 <= y2
  | s => y2 <= y1
  end.

(* 延長部分でも PrimitiveSegment の向きに逆行しない。弱い単調性なので、
   水平または垂直になる区間は許している。 *)
Axiom embedded_head_extension_monotone :
  forall s v h c t1 t2,
    embed (v, h, c) s ->
    t1 <= t2 -> t2 <= 0 ->
    horizontal_order h (fst (point s t1)) (fst (point s t2))
    /\ vertical_order v (snd (point s t1)) (snd (point s t2)).

Axiom embedded_last_extension_monotone :
  forall s v h c t1 t2,
    embed (v, h, c) s ->
    1 <= t1 -> t1 <= t2 ->
    horizontal_order h (fst (point s t1)) (fst (point s t2))
    /\ vertical_order v (snd (point s t1)) (snd (point s t2)).

(* セグメント列の端点座標境界。 *)

Definition rect_height (Rc : Rect) : R := ry1 Rc - ry0 Rc.

Definition segment_coord_min (coord : Point -> R) (s : Segment) : R :=
  Rmin (coord (init s)) (coord (term s)).

Definition segment_coord_max (coord : Point -> R) (s : Segment) : R :=
  Rmax (coord (init s)) (coord (term s)).

(* 非空なセグメント列の全端点における座標の最小値・最大値。 *)
Fixpoint segments_coord_min
  (coord : Point -> R) (s : Segment) (rest : list Segment) : R :=
  match rest with
  | [] => segment_coord_min coord s
  | t :: rest' =>
      Rmin (segment_coord_min coord s) (segments_coord_min coord t rest')
  end.

Fixpoint segments_coord_max
  (coord : Point -> R) (s : Segment) (rest : list Segment) : R :=
  match rest with
  | [] => segment_coord_max coord s
  | t :: rest' =>
      Rmax (segment_coord_max coord s) (segments_coord_max coord t rest')
  end.

(* 空列の bbox は退化した原点とする。非空列では全端点の厳密な bbox。 *)
Definition bbox_of (ls : list Segment) : Rect :=
  match ls with
  | [] => mkRect 0 0 0 0
  | first :: rest =>
      mkRect
        (segments_coord_min (fun p : Point => fst p) first rest)
        (segments_coord_min (fun p : Point => snd p) first rest)
        (segments_coord_max (fun p : Point => fst p) first rest)
        (segments_coord_max (fun p : Point => snd p) first rest)
  end.

Lemma segments_coord_bounds : forall coord s rest t,
  In t (s :: rest) ->
  segments_coord_min coord s rest <= segment_coord_min coord t
  /\ segment_coord_max coord t <= segments_coord_max coord s rest.
Proof.
  intros coord s rest. revert s.
  induction rest as [|a rest IH]; intros s t Hin.
  - simpl in Hin. destruct Hin as [<- | []]. split; reflexivity.
  - simpl in Hin |- *.
    destruct Hin as [<- | Hin].
    + split; [apply Rmin_l | apply Rmax_l].
    + destruct (IH a t Hin) as [Hmin Hmax].
      split.
      * eapply Rle_trans; [apply Rmin_r | exact Hmin].
      * eapply Rle_trans; [exact Hmax | apply Rmax_r].
Qed.

Lemma onSegment_y_bounds : forall s p,
  onSegment s p ->
  segment_coord_min (fun q : Point => snd q) s <= snd p
  /\ snd p <= segment_coord_max (fun q : Point => snd q) s.
Proof.
  intros s p Hp.
  destruct (segment_in_rectangle_or_endpoints s p Hp)
    as [-> | [-> | Hinside]].
  - split; [apply Rmin_l | apply Rmax_l].
  - split; [apply Rmin_r | apply Rmax_r].
  - unfold segment_coord_min, segment_coord_max.
    unfold in_open_segment_rectangle, in_rect, rect_between in Hinside.
    simpl in Hinside. lra.
Qed.

Lemma bbox_of_bounds :
  forall sub p, onSegmentlist sub p ->
    ry0 (bbox_of sub) <= snd p <= ry1 (bbox_of sub).
Proof.
  intros sub p [t [Ht Hp]].
  destruct sub as [|s rest]; [contradiction|].
  change
    (segments_coord_min (fun q : Point => snd q) s rest <= snd p
     <= segments_coord_max (fun q : Point => snd q) s rest).
  destruct (segments_coord_bounds (fun q : Point => snd q) s rest t Ht)
    as [Hmin Hmax].
  destruct (onSegment_y_bounds t p Hp) as [Hlo Hhi].
  split; lra.
Qed.
