Require Export Sparse.ClassifyInvariant.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Relations.Operators_Properties.

(* 順序閉包から構成した分類器が外部仕様を満たすことの証明。 *)
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

(* Up 用不変量を一辺ずつ保存する。各辺の局所幾何をここで直接選び、
   中間的な「core/end 保存則」レコードは作らない。 *)
Lemma up_path_invariant_preserved_by_order_path :
  forall l sub r,
    ClassificationContext l sub r ->
    forall p q,
      endpoint_up_reachable l sub r p ->
      up_path_invariant l sub r p ->
      endpoint_order_path l sub r p q ->
      up_path_invariant l sub r q.
Proof.
  intros l sub r Hctx p q Hreachable Hp Hpath.
  revert Hreachable Hp.
  induction Hpath as [p | p next q Hfirst Htail IH];
    intros Hreachable Hp.
  - exact Hp.
  - assert (HnextReachable : endpoint_up_reachable l sub r next).
    { eapply endpoint_up_reachable_step; eauto. }
    apply (IH HnextReachable).
    destruct Hfirst as [p next Hcore | p next Hend].
    + destruct Hcore as
        [seg p next Hin HpEnd HnextEnd Hheight
        | i j s t ps pt Hs Ht Hfar Hover Hps Hpt HptNotSub Hheight].
      * exact (same_segment_upward_preserves_up_path_invariant
                 l sub r seg p next Hctx Hin HpEnd HnextEnd Hheight Hp).
      * exact (nonadjacent_upward_preserves_up_path_invariant
                 l sub r i j s t ps pt Hctx Hs Ht Hfar Hover Hps Hpt
                 HptNotSub Hheight Hreachable Hp).
    + destruct Hend.
      * eapply barrier_reverse_step_preserves_up_path_invariant; eauto.
        now apply barrier_reverse_head_north_cx with (hor := hor).
      * eapply barrier_reverse_step_preserves_up_path_invariant; eauto.
        now apply barrier_reverse_head_south_cc with (hor := hor).
      * eapply barrier_reverse_step_preserves_up_path_invariant; eauto.
        now apply barrier_reverse_last_north_cc with (hor := hor).
      * eapply barrier_reverse_step_preserves_up_path_invariant; eauto.
        now apply barrier_reverse_last_south_cx with (hor := hor).
      * eapply head_below_last_preserves_up_path_invariant; eauto.
      * eapply last_below_head_preserves_up_path_invariant; eauto.
      * eapply head_below_segment_preserves_up_path_invariant; eauto.
      * eapply segment_below_head_preserves_up_path_invariant; eauto.
      * eapply last_below_segment_preserves_up_path_invariant; eauto.
      * eapply segment_below_last_preserves_up_path_invariant; eauto.
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
  assert (Hreachable : endpoint_up_reachable l sub r upper).
  { now apply endpoint_up_reachable_seed. }
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

(* sub に隣接する左端セグメントの上下外側では、順序閉包はその
   長方形へ向かう分類を生成しない。隣接性による例外は設けない。 *)
Lemma classify_below_terminal_not_up :
  forall l sub r,
    ClassificationContext l sub r ->
    l <> [] ->
    forall p,
      endpoint_of (l ++ sub ++ r) p ->
      snd p < ry0 (rect_of [last_segment l]) ->
      classify l sub r p <> RegUp.
Admitted.

(* 右端についての双対。sub と共有する端点を持つ隣接セグメントも
   通常の端点と同じ制約に含める。 *)
Lemma classify_below_initial_not_up :
  forall l sub r,
    ClassificationContext l sub r ->
    r <> [] ->
    forall p,
      endpoint_of (l ++ sub ++ r) p ->
      snd p < ry0 (rect_of [hd_segment r]) ->
      classify l sub r p <> RegUp.
Admitted.

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
  - intros i j s0 t ps pt Hs Ht Hij Hover Hps Hpt HptNotSub Hy.
    eapply endpoint_order_classified; eauto.
    + exists s0. split; [eapply nth_error_In; eauto | exact Hps].
    + exists t. split; [eapply nth_error_In; eauto | exact Hpt].
    + apply rt_step.
      apply order_core_step.
      exact (order_nonadjacent l sub r i j s0 t ps pt
               Hs Ht Hij Hover Hps Hpt HptNotSub Hy).
  - exact (classify_below_terminal_not_up l sub r Hctx).
  - exact (classify_below_initial_not_up l sub r Hctx).
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

(* 分類された端点の上下移動。 *)

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

(* Up 以外の分類は点を上昇させない。sub 隣接セグメントの固定端点と
   下側長方形との分離を保存する際に用いる。 *)
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
