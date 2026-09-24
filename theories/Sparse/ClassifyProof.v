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
Lemma endpoint_order_up_down_path_meets_sub :
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
Admitted.

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

(* sub 上から出た順序パスは、sub 外だけを通って Down source へ
   到達できない。末尾側まで含む下側の局所的な障壁補題である。 *)
Lemma endpoint_order_sub_first_exit_to_down_impossible :
  forall l sub r,
    ClassificationContext l sub r ->
    forall before after lower,
      onSegmentlist sub before ->
      endpoint_order_step l sub r before after ->
      ~ onSegmentlist sub after ->
      endpoint_order_path l sub r after lower ->
      endpoint_down_seed l sub r lower ->
      False.
Admitted.

Lemma up_seed_not_reaches_sub : forall l sub r,
  ClassificationContext l sub r ->
  forall upper lower,
    endpoint_up_seed l sub r upper ->
    onSegmentlist sub lower ->
    ~ endpoint_order l sub r upper lower.
Proof.
  intros l sub r Hctx upper lower Hup Hsub Horder.
  assert (Hinitial : up_path_invariant l sub r upper).
  { now apply endpoint_up_seed_satisfies_up_path_invariant. }
  assert (Hreachable : endpoint_up_reachable l sub r upper).
  { now apply endpoint_up_reachable_seed. }
  assert (Hfinal : up_path_invariant l sub r lower).
  { eapply up_path_invariant_preserved_by_order_path; eauto.
    now apply (proj1 (endpoint_order_path_iff l sub r upper lower)). }
  exact (up_path_invariant_not_on_sub
           l sub r lower Hctx Hfinal Hsub).
Qed.

Lemma sub_not_reaches_down_seed : forall l sub r,
  ClassificationContext l sub r ->
  forall upper lower,
    onSegmentlist sub upper ->
    endpoint_down_seed l sub r lower ->
    ~ endpoint_order l sub r upper lower.
Proof.
  intros l sub r Hctx upper lower Hsub Hdown Horder.
  pose proof (proj1 (endpoint_order_path_iff l sub r upper lower) Horder)
    as Hpath.
  destruct (endpoint_order_path_first_exit
              l sub r (onSegmentlist sub) upper lower Hpath Hsub
              (endpoint_down_seed_not_on_sub l sub r lower Hctx Hdown))
    as [before [after [Hprefix [Hstep [Hbefore [Hafter Hsuffix]]]]]].
  exact (endpoint_order_sub_first_exit_to_down_impossible
           l sub r Hctx before after lower Hbefore Hstep Hafter Hsuffix Hdown).
Qed.

Lemma up_seed_not_reaches_down_seed : forall l sub r,
  ClassificationContext l sub r ->
  forall upper lower,
    endpoint_up_seed l sub r upper ->
    endpoint_down_seed l sub r lower ->
    ~ endpoint_order l sub r upper lower.
Proof.
  intros l sub r Hctx upper lower Hup Hdown Horder.
  pose proof (proj1 (endpoint_order_path_iff l sub r upper lower) Horder)
    as Hpath.
  destruct (endpoint_order_up_down_path_meets_sub
              l sub r Hctx upper lower Hup Hdown Hpath)
    as [at_sub [Hat [Hprefix _]]].
  apply (up_seed_not_reaches_sub l sub r Hctx upper at_sub Hup Hat).
  now apply (proj2 (endpoint_order_path_iff l sub r upper at_sub)).
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

(* Up と判定された端点には、seed からの順序経路に沿って保存された
   中央の上下関係または左右の障壁証明書がある。 *)
Lemma classify_up_has_up_path_invariant : forall l sub r p,
  ClassificationContext l sub r ->
  classify l sub r p = RegUp ->
  up_path_invariant l sub r p.
Proof.
  intros l sub r p Hctx Hclass.
  destruct (classify_up_forced l sub r p Hclass)
    as [seed [Hseed Horder]].
  eapply (up_path_invariant_preserved_by_order_path
            l sub r Hctx seed p).
  - now apply endpoint_up_reachable_seed.
  - now apply endpoint_up_seed_satisfies_up_path_invariant.
  - now apply (proj1 (endpoint_order_path_iff l sub r seed p)).
Qed.

(* 蓋でない左境界は東向きで、その終点が sub の左 anchor である。 *)
Lemma ordinary_terminal_boundary_data : forall l sub r,
  ClassificationContext l sub r ->
  l <> [] ->
  ~ terminal_lid l ->
  fst (init (last_segment l)) < fst (term (last_segment l))
  /\ term (last_segment l) = sub_left_anchor sub.
Proof.
  intros l sub r Hctx Hl HnotLid.
  assert (Hsub : sub <> []) by now apply context_sub_nonempty with (l := l) (r := r).
  assert (Htail : sub ++ r <> []).
  { destruct sub; [contradiction | discriminate]. }
  assert (Hjoin : term (last_segment l) = init (hd_segment (sub ++ r))).
  { apply connected_app_junction; [|exact Hl|exact Htail].
    exact (context_whole_connected l sub r Hctx). }
  assert (Hhd : hd_segment (sub ++ r) = hd_segment sub).
  { symmetry. unfold hd_segment. now apply hd_app. }
  split.
  - destruct (total_order_T
                (fst (init (last_segment l)))
                (fst (term (last_segment l)))) as [[Hlt | Heq] | Hgt].
    + exact Hlt.
    + exfalso. apply (neq_init_term_x (last_segment l)). exact Heq.
    + exfalso. apply HnotLid. now split.
  - unfold sub_left_anchor. now rewrite <- Hhd.
Qed.

(* sub の同じ x に下側の本体点を持つ非隣接セグメントの端点は、
   その本体点を証人とする Down seed なので RegDown になる。 *)
Lemma nonadjacent_below_sub_point_classified_down : forall l sub r t p z,
  ClassificationContext l sub r ->
  In t (nonadjacent_sides l r) ->
  endpoint_of_seg t p ->
  onSegment t z ->
  in_sub_x_range sub z ->
  below_sub_at_x sub z ->
  classify l sub r p = RegDown.
Proof.
  intros l sub r t p z Hctx Ht Hp Hz Hrange Hbelow.
  apply (classify_forced_down l sub r p Hctx).
  - exists t. split; [now apply nonadjacent_sides_in_whole | exact Hp].
  - apply endpoint_seed_forced_down. split.
    + exists t. split; [now apply nonadjacent_sides_in_whole | exact Hp].
    + left. exists t, z. split; [exact Ht |].
      split; [exact Hp |]. split; [exact Hz |].
      split; [exact Hrange | exact Hbelow].
Qed.

(* 北東向きセグメントの直後にある rising な末尾 trace は、接続点より
   左下へ戻れない。これは dc の三つの可能形と end trace の単調性だけ。 *)
Lemma dc_after_northeast_cannot_return_left_below :
  forall ps1 ps2 s1 s2 p,
    dc ps1 ps2 ->
    embed ps1 s1 ->
    embed ps2 s2 ->
    term s1 = init s2 ->
    fst (init s1) < fst (term s1) ->
    snd (init s1) < snd (term s1) ->
    onLastSegment s2 p ->
    fst p < fst (init s2) ->
    snd p < snd (init s2) ->
    False.
Proof.
  intros [[v h] c] ps2 s1 s2 p Hdc Hembed1 Hembed2 Hjoin
    Hx1 Hy1 Hp Hpx Hpy.
  destruct v, h.
  - inversion Hdc; subst; clear Hdc.
    + pose proof (embedded_last_trace_vertical_bound
                    s2 n e (i_c c) p Hembed2 Hp). cbn in H. lra.
    + pose proof (embedded_last_trace_horizontal_bound
                    s2 s e cx p Hembed2 Hp). cbn in H.
      pose proof (f_equal fst Hjoin). cbn in H0. lra.
    + pose proof (embedded_last_trace_vertical_bound
                    s2 n w cx p Hembed2 Hp). cbn in H. lra.
  - pose proof (w_end_relation s1 n c Hembed1). lra.
  - pose proof (s_end_relation s1 e c Hembed1). lra.
  - pose proof (w_end_relation s1 s c Hembed1). lra.
Qed.

Lemma classification_context_app_boundary_data :
  forall l sub r left right,
    ClassificationContext l sub r ->
    l ++ sub ++ r = left ++ right ->
    left <> [] ->
    right <> [] ->
    exists ps1 ps2,
      embed ps1 (last_segment left)
      /\ embed ps2 (hd_segment right)
      /\ dc ps1 ps2
      /\ term (last_segment left) = init (hd_segment right).
Proof.
  intros l sub r left right Hctx Hwhole Hleft Hright.
  destruct (context_whole_embedded l sub r Hctx) as [ds [sc [_ Hembed]]].
  rewrite Hwhole in Hembed.
  assert (Hlen : (0 < length left)%nat).
  { destruct left; [contradiction | simpl; lia]. }
  assert (Hlast :
      nth_error (left ++ right) (length left - 1) =
        Some (last_segment left)).
  { rewrite nth_error_app1 by lia.
    unfold last_segment. now apply nth_error_last. }
  assert (Hhead :
      nth_error (left ++ right) (S (length left - 1)) =
        Some (hd_segment right)).
  { replace (S (length left - 1)) with (length left) by lia.
    rewrite nth_error_app2 by lia.
    replace (length left - length left)%nat with 0%nat by lia.
    destruct right; [contradiction | reflexivity]. }
  exact (embed_scurve_adjacent_data
           sc (left ++ right) (length left - 1)
           (last_segment left) (hd_segment right)
           Hembed Hlast Hhead).
Qed.

(* 通常左境界の下端高さにある rising 障壁点は、その境界セグメントの
   左端より右へ入れない。非隣接時は closed sparse、隣接時だけ dc。 *)
Lemma ordinary_terminal_barrier_floor_not_right :
  forall l sub r side b,
    ClassificationContext l sub r ->
    l <> [] ->
    ~ terminal_lid l ->
    on_barrier_trace side (l ++ sub ++ r) b ->
    right_rising_barrier side (l ++ sub ++ r) ->
    snd b = ry0 (rect_of [last_segment l]) ->
    fst b < fst (sub_left_anchor sub) ->
    fst b <= rx0 (rect_of [last_segment l]).
Proof.
  intros l sub r side b Hctx Hl HnotLid Htrace Hrising Hby Hbx.
  destruct (ordinary_terminal_boundary_data l sub r Hctx Hl HnotLid)
    as [Heast Hjoin].
  apply Rnot_lt_le. intro HinsideLeft.
  assert (HinsideRight : fst b < fst (term (last_segment l))).
  { now rewrite Hjoin. }
  assert (HinitLeft : fst (init (last_segment l)) < fst b).
  { change (Rmin (fst (init (last_segment l)))
                 (fst (term (last_segment l))) < fst b) in HinsideLeft.
    rewrite Rmin_left in HinsideLeft by lra. exact HinsideLeft. }
  assert (HbBox : in_segment_rect_or_endpoints (last_segment l) b).
  { unfold in_segment_rect_or_endpoints, in_closed_rect, rect_of. cbn.
    split.
    - rewrite Rmin_left, Rmax_right by lra. lra.
    - rewrite Hby. split; [apply Rle_refl | apply Rminmax]. }
  destruct (exists_last Hl) as [prefix [a Hlshape]].
  subst l.
  assert (Hlast : last_segment (prefix ++ [a]) = a).
  { now apply last_app_nonnil. }
  rewrite Hlast in Heast, Hjoin, HinsideRight, HinitLeft, HbBox, Hby.
  set (tail := sub ++ r).
  assert (Htail : tail <> []).
  { unfold tail. destruct sub; [now apply context_sub_nonempty in Hctx | discriminate]. }
  assert (Hdecomp :
      (prefix ++ [a]) ++ sub ++ r = prefix ++ [a] ++ tail).
  { unfold tail. repeat rewrite app_assoc. reflexivity. }
  pose proof (context_sparse (prefix ++ [a]) sub r Hctx
                prefix a tail Hdecomp) as Haround.
  destruct Haround as [Hext Hrect].
  rewrite Hdecomp in Htrace, Hrising.
  destruct side.
  - cbn in Htrace, Hrising.
    destruct Htrace as [u [Hu Hub]].
    destruct prefix as [|h prefix']; cbn in Hub, Hrising.
    + assert (HinitTrace : onHeadSegment a (init a)).
      { exists 0. split; [lra | reflexivity]. }
      assert (HbTrace : onHeadSegment a b).
      { exists u. split; [exact Hu | exact Hub]. }
      pose proof (proj1 (Hrising (init a) b HinitTrace HbTrace) HinitLeft).
      change (snd b = Rmin (snd (init a)) (snd (term a))) in Hby.
      pose proof (Rmin_l (snd (init a)) (snd (term a))). lra.
    + destruct (Rlt_dec u 0) as [HuStrict | HuBody].
      * apply (Hext b).
        -- left. split; [discriminate |].
           unfold onHead_extend_strict. exists u. split; [exact HuStrict |].
           exact Hub.
        -- exact HbBox.
      * assert (HbBody : onSegment h b).
        { exists u. split; [lra | exact Hub]. }
        destruct prefix' as [|h' prefix''].
        -- assert (HwholeConn : connected ([h] ++ a :: tail)).
           { change (connected (([h] ++ [a]) ++ sub ++ r)).
             exact (context_whole_connected (h :: [a]) sub r Hctx). }
           assert (Hjunction : term h = init a).
           { eapply connected_app_junction with (l := [h]) (r := a :: tail).
             - exact HwholeConn.
             - discriminate.
             - discriminate. }
           assert (HjointTrace : onHeadSegment h (term h)).
           { exists 1. split; [lra | reflexivity]. }
           assert (HbTrace : onHeadSegment h b).
           { exists u. split; [exact Hu | exact Hub]. }
           assert (HjointLeft : fst (term h) < fst b) by now rewrite Hjunction.
           pose proof (proj1 (Hrising (term h) b HjointTrace HbTrace)
                        HjointLeft).
           change (snd b = Rmin (snd (init a)) (snd (term a))) in Hby.
           pose proof (Rmin_l (snd (init a)) (snd (term a))).
           rewrite Hjunction in H. lra.
        -- apply (Hrect h b).
           ++ unfold nonadjacent_sides. rewrite in_app_iff. left. simpl. now left.
           ++ exact (segment_in_rect_or_endpoints h b HbBody).
           ++ exact HbBox.
  - cbn in Htrace, Hrising.
    destruct Htrace as [u [Hu Hub]].
    destruct (Rlt_dec 1 u) as [HuStrict | HuBody].
    + apply (Hext b).
      * right. split; [exact Htail |].
        unfold onLast_extend_strict. exists u. split; [exact HuStrict |].
        exact Hub.
      * exact HbBox.
    + assert (HbBody : onSegment (last_segment (prefix ++ [a] ++ tail)) b).
      { exists u. split; [lra | exact Hub]. }
      destruct tail as [|s tail']; [contradiction |].
      destruct tail' as [|s' tail''].
      * assert (HlastWhole : last_segment (prefix ++ [a; s]) = s).
        { rewrite (last_app_nonnil prefix [a; s]) by discriminate.
          reflexivity. }
        rewrite HlastWhole in Hub.
        unfold right_rising_barrier, on_barrier_trace,
          barrier_segment in Hrising. cbn in Hrising.
        rewrite HlastWhole in Hrising.
        assert (HwholeEq :
            (prefix ++ [a]) ++ sub ++ r = (prefix ++ [a]) ++ [s]).
        { rewrite Hdecomp. repeat rewrite app_assoc. reflexivity. }
        assert (HleftNE : prefix ++ [a] <> []).
        { intros Hnil. apply app_eq_nil in Hnil. destruct Hnil as [_ Hnil].
          discriminate. }
        destruct (classification_context_app_boundary_data
                    (prefix ++ [a]) sub r (prefix ++ [a]) [s]
                    Hctx HwholeEq HleftNE ltac:(discriminate))
          as [ps1 [ps2 [Hemb1 [Hemb2 [Hdc Hboundary]]]]].
        rewrite Hlast in Hemb1, Hboundary.
        cbn in Hemb2, Hboundary.
        assert (HinitTrace : onLastSegment s (init s)).
        { exists 0. split; [lra | reflexivity]. }
        assert (HbTrace : onLastSegment s b).
        { exists u. split; [exact Hu | exact Hub]. }
        assert (HbBelowInit : snd b < snd (init s)).
        { apply (proj1 (Hrising b (init s) HbTrace HinitTrace)).
          now rewrite <- Hboundary. }
        assert (HaNorth : snd (init a) < snd (term a)).
        { change (snd b = Rmin (snd (init a)) (snd (term a))) in Hby.
          pose proof (f_equal snd Hboundary) as HboundaryY. cbn in HboundaryY.
          unfold Rmin in Hby. destruct Rle_dec; lra. }
        assert (HbLeftInit : fst b < fst (init s)).
        { now rewrite <- Hboundary. }
        exact (dc_after_northeast_cannot_return_left_below
                 ps1 ps2 a s b Hdc Hemb1 Hemb2 Hboundary Heast HaNorth
                 HbTrace HbLeftInit HbBelowInit).
      * assert (HlastTail :
            last_segment (s :: s' :: tail'') = last_segment (s' :: tail'')).
        { change (last_segment ([s] ++ (s' :: tail'')) =
                  last_segment (s' :: tail'')).
          apply last_app_nonnil. discriminate. }
        assert (HlastWhole :
            last_segment (prefix ++ [a] ++ s :: s' :: tail'') =
              last_segment (s :: s' :: tail'')).
        { rewrite (last_app_nonnil prefix ([a] ++ s :: s' :: tail''))
            by discriminate.
          apply last_app_nonnil. discriminate. }
        rewrite HlastWhole in HbBody.
        apply (Hrect (last_segment (s :: s' :: tail'')) b).
        -- unfold nonadjacent_sides. rewrite in_app_iff. right.
           change (In (last_segment (s :: s' :: tail'')) (s' :: tail'')).
           rewrite HlastTail. apply last_In. discriminate.
        -- exact (segment_in_rect_or_endpoints _ _ HbBody).
        -- exact HbBox.
Qed.

(* 左下の certificate core は通常境界の下端高さまで実在する。そこでの
   障壁点は、通常境界との重なりにより target の右端より左にある。 *)
Lemma ordinary_terminal_core_reaches_floor :
  forall l sub r t p side,
    ClassificationContext l sub r ->
    l <> [] ->
    ~ terminal_lid l ->
    segment_x_ranges_overlap t (last_segment l) ->
    ry1 (rect_of [t]) < ry0 (rect_of [last_segment l]) ->
    endpoint_of_seg t p ->
    left_barrier_core side l sub r p ->
    exists b,
      on_barrier_trace side (l ++ sub ++ r) b
      /\ snd b = ry0 (rect_of [last_segment l])
      /\ fst p < fst b
      /\ fst b <= rx0 (rect_of [last_segment l])
      /\ fst b <= rx1 (rect_of [t]).
Proof.
  intros l sub r t p side Hctx Hl HnotLid Hover Hbelow Hp Hcore.
  destruct (ordinary_terminal_boundary_data l sub r Hctx Hl HnotLid)
    as [_ Hjoin].
  pose proof Hcore as Hcore'.
  unfold left_barrier_core in Hcore'. cbn in Hcore'.
  destruct Hcore' as [Hwhole [Hrising [Hpx [Hpy Hopen]]]].
  assert (HpBox : in_segment_rect_or_endpoints t p).
  { apply segment_in_rect_or_endpoints. destruct Hp as [-> | ->];
      [apply onInit | apply onTerm]. }
  unfold in_segment_rect_or_endpoints, in_closed_rect in HpBox.
  destruct HpBox as [_ [_ HpTop]].
  assert (HpFloor : snd p < ry0 (rect_of [last_segment l])) by lra.
  assert (HfloorAnchor :
      ry0 (rect_of [last_segment l]) <= snd (sub_left_anchor sub)).
  { change (Rmin (snd (init (last_segment l)))
                 (snd (term (last_segment l))) <=
            snd (sub_left_anchor sub)).
    rewrite <- Hjoin. apply Rmin_r. }
  destruct (Hopen (ry0 (rect_of [last_segment l]))
              ltac:(lra)) as [x [[Hpxx Hxanchor] Htrace]].
  set (b := (x, ry0 (rect_of [last_segment l]))).
  assert (HbTrace : on_barrier_trace side (l ++ sub ++ r) b).
  { exact Htrace. }
  assert (HbFloor : snd b = ry0 (rect_of [last_segment l])) by reflexivity.
  assert (HbBoundary : fst b <= rx0 (rect_of [last_segment l])).
  { eapply (ordinary_terminal_barrier_floor_not_right
              l sub r side b Hctx Hl HnotLid); eauto. }
  assert (HbTarget : fst b <= rx1 (rect_of [t])).
  { unfold segment_x_ranges_overlap in Hover. cbn in Hpxx, Hxanchor.
    lra. }
  exists b. repeat split; assumption.
Qed.

(* 通常高さの証明書では、同じ高さの障壁点が target の閉長方形へ
   入る。同一・非隣接は単射性と sparse、隣接だけを dc で処理する。 *)
Lemma ordinary_terminal_at_level_collision_impossible :
  forall l sub r t p side,
    ClassificationContext l sub r ->
    l <> [] ->
    ~ terminal_lid l ->
    In t (nonadjacent_sides l r) ->
    segment_x_ranges_overlap t (last_segment l) ->
    ry1 (rect_of [t]) < ry0 (rect_of [last_segment l]) ->
    endpoint_of_seg t p ->
    rx1 (rect_of [t]) < fst (sub_left_anchor sub) ->
    left_barrier_core side l sub r p ->
    left_barrier_at_level side l sub r p ->
    False.
Proof.
  intros l sub r t p side Hctx Hl HnotLid Ht Hover Hbelow Hp HtLeft
    Hcore Hlevel.
  destruct (ordinary_terminal_core_reaches_floor
              l sub r t p side Hctx Hl HnotLid Hover Hbelow Hp Hcore)
    as [b [HbTrace [HbY [Hpb [HbBoundary HbTarget]]]]].
  destruct Hlevel as [xb [[Hpxb HxbAnchor] HxbTrace]].
  assert (HpFloor : snd p < snd b).
  { rewrite HbY. assert (HpBox : in_segment_rect_or_endpoints t p).
    { apply segment_in_rect_or_endpoints. destruct Hp as [-> | ->];
        [apply onInit | apply onTerm]. }
    unfold in_segment_rect_or_endpoints, in_closed_rect in HpBox.
    destruct HpBox as [_ [_ HpTop]]. lra. }
  pose proof Hcore as Hcore'.
  unfold left_barrier_core in Hcore'. cbn in Hcore'.
  destruct Hcore' as [_ [Hrising _]].
  assert (Hxbb : xb < fst b).
  { apply (proj2 (Hrising (xb, snd p) b HxbTrace HbTrace)). cbn. exact HpFloor. }
  assert (HxbBox : in_segment_rect_or_endpoints t (xb, snd p)).
  { assert (HpBox : in_segment_rect_or_endpoints t p).
    { apply segment_in_rect_or_endpoints. destruct Hp as [-> | ->];
        [apply onInit | apply onTerm]. }
    unfold in_segment_rect_or_endpoints, in_closed_rect in HpBox |- *.
    destruct p as [xp yp]. cbn in *. destruct HpBox as [[Hpx0 Hpx1] [Hpy0 Hpy1]].
    split; cbn; split; lra. }
  (* 残る有限の場合分けは、障壁が target と同一・遠隔・隣接の順。
     隣接二場合は head/last trace 補題と dc 補題へ還元する。 *)
Admitted.

(* extension seed 自身が target の端点の場合。異なるセグメントなら
   sparse/隣接交差、同じ end なら trace bounds で floor 点を排除する。 *)
Lemma ordinary_terminal_extension_root_impossible :
  forall l sub r t p side,
    ClassificationContext l sub r ->
    l <> [] ->
    ~ terminal_lid l ->
    In t (nonadjacent_sides l r) ->
    segment_x_ranges_overlap t (last_segment l) ->
    ry1 (rect_of [t]) < ry0 (rect_of [last_segment l]) ->
    endpoint_of_seg t p ->
    rx1 (rect_of [t]) < fst (sub_left_anchor sub) ->
    left_barrier_core side l sub r p ->
    barrier_extension_seed l sub r side p ->
    on_barrier_trace side (l ++ sub ++ r) p ->
    False.
Proof.
  intros l sub r t p side Hctx Hl HnotLid Ht Hover Hbelow Hp HtLeft
    Hcore Hseed HrootTrace.
  destruct (ordinary_terminal_core_reaches_floor
              l sub r t p side Hctx Hl HnotLid Hover Hbelow Hp Hcore)
    as [b [HbTrace [HbY [Hpb [HbBoundary HbTarget]]]]].
  (* floor 点は target の x 範囲内まで達する。自己障壁なら end trace の
     bounds、別障壁なら closed sparse または隣接 junction で矛盾する。 *)
Admitted.

(* reverse root が別セグメントの端点でもある場合。共有点が junction
   なら reverse の四形と dc、遠隔なら closed sparse で排除する。 *)
Lemma ordinary_terminal_distinct_reverse_root_impossible :
  forall l sub r t p side previous,
    ClassificationContext l sub r ->
    l <> [] ->
    ~ terminal_lid l ->
    In t (nonadjacent_sides l r) ->
    segment_x_ranges_overlap t (last_segment l) ->
    ry1 (rect_of [t]) < ry0 (rect_of [last_segment l]) ->
    endpoint_of_seg t p ->
    rx1 (rect_of [t]) < fst (sub_left_anchor sub) ->
    left_barrier_core side l sub r p ->
    barrier_reverse_step l sub r side previous p ->
    on_barrier_trace side (l ++ sub ++ r) p ->
    t <> barrier_segment side (l ++ sub ++ r) ->
    False.
Proof.
  intros l sub r t p side previous Hctx Hl HnotLid Ht Hover Hbelow Hp
    HtLeft Hcore Hreverse HrootTrace Hdistinct.
  destruct (ordinary_terminal_core_reaches_floor
              l sub r t p side Hctx Hl HnotLid Hover Hbelow Hp Hcore)
    as [b [HbTrace [HbY [Hpb [HbBoundary HbTarget]]]]].
  (* strict extension、非隣接本体、前後一つの隣接本体に分ける。最後の
     二枝は既存の rising-head/last の dc 補題で外向きを得る。 *)
Admitted.

(* 通常左境界の完全下側にある端点が境界より左で Up なら、実際の
   到達経路と証明書の生成形を同時に追って衝突を導く必要がある。
   任意の barrier core だけでは、障壁が通常境界自身の場合を除けない。 *)
Lemma ordinary_terminal_gate_blocks_left_certificate : forall l sub r t p,
  ClassificationContext l sub r ->
  l <> [] ->
  ~ terminal_lid l ->
  In t (nonadjacent_sides l r) ->
  segment_x_ranges_overlap t (last_segment l) ->
  ry1 (rect_of [t]) < ry0 (rect_of [last_segment l]) ->
  endpoint_of_seg t p ->
  rx1 (rect_of [t]) < fst (sub_left_anchor sub) ->
  left_up_certificate l sub r p ->
  False.
Proof.
  intros l sub r t p Hctx Hl HnotLid Ht Hover Hbelow Hp HtLeft Hcertificate.
  revert p Hp Hcertificate.
  fix IH 3.
  intros p Hp Hcertificate.
  destruct Hcertificate as
    [side root p Hcore Hseed HrootTrace Hposition
    | side root previous p Hcore Hreverse Hprevious HrootTrace Hposition].
  - destruct Hposition as [Hlevel | Hroot].
    + exact (ordinary_terminal_at_level_collision_impossible
               l sub r t p side Hctx Hl HnotLid Ht Hover Hbelow Hp HtLeft
               Hcore Hlevel).
    + subst root.
      exact (ordinary_terminal_extension_root_impossible
               l sub r t p side Hctx Hl HnotLid Ht Hover Hbelow Hp HtLeft
               Hcore Hseed HrootTrace).
  - destruct Hposition as [Hlevel | Hroot].
    + exact (ordinary_terminal_at_level_collision_impossible
               l sub r t p side Hctx Hl HnotLid Ht Hover Hbelow Hp HtLeft
               Hcore Hlevel).
    + subst root.
      destruct (classic (t = barrier_segment side (l ++ sub ++ r)))
        as [Hsame | Hdistinct].
      * destruct Hp as [Hp | Hp].
        -- subst p.
           assert (Hother : term t = previous).
           { exact (barrier_reverse_step_other_endpoint
                      l sub r side previous (init t) t (term t)
                      Hreverse Hsame (or_introl eq_refl) (or_intror eq_refl)
                      (neq_init_term t)). }
           rewrite <- Hother in Hprevious.
           exact (IH (term t) (or_intror eq_refl) Hprevious).
        -- subst p.
           assert (Hother : init t = previous).
           { exact (barrier_reverse_step_other_endpoint
                      l sub r side previous (term t) t (init t)
                      Hreverse Hsame (or_intror eq_refl) (or_introl eq_refl)
                      (not_eq_sym (neq_init_term t))). }
           rewrite <- Hother in Hprevious.
           exact (IH (init t) (or_introl eq_refl) Hprevious).
      * exact (ordinary_terminal_distinct_reverse_root_impossible
                 l sub r t p side previous Hctx Hl HnotLid Ht Hover Hbelow
                 Hp HtLeft Hcore Hreverse HrootTrace Hdistinct).
Qed.

(* 蓋でない左通常境界の下では、固定接続点までの空いた閉長方形と
   その外側から伸びる rising 障壁により Up 到達を排除する。 *)
Lemma classify_below_terminal_not_up :
  forall l sub r,
    ClassificationContext l sub r ->
    l <> [] ->
    ~ terminal_lid l ->
    forall t p,
      In t (nonadjacent_sides l r) ->
      segment_x_ranges_overlap t (last_segment l) ->
      ry1 (rect_of [t]) < ry0 (rect_of [last_segment l]) ->
      endpoint_of_seg t p ->
      classify l sub r p <> RegUp.
Proof.
  intros l sub r Hctx Hl HnotLid t p Ht Hover Hbelow Hp Hup.
  destruct (ordinary_terminal_boundary_data l sub r Hctx Hl HnotLid)
    as [Heast Hjoin].
  assert (HpY : snd p < snd (sub_left_anchor sub)).
  { change (Rmax (snd (init t)) (snd (term t)) <
            Rmin (snd (init (last_segment l)))
                 (snd (term (last_segment l)))) in Hbelow.
    assert (HpMax : snd p <= Rmax (snd (init t)) (snd (term t))).
    { destruct Hp as [-> | ->]; [apply Rmax_l | apply Rmax_r]. }
    pose proof (Rmin_r (snd (init (last_segment l)))
                       (snd (term (last_segment l)))) as Hmin.
    assert (HpTerm : snd p < snd (term (last_segment l))) by lra.
    now rewrite Hjoin in HpTerm. }
  destruct (Rlt_dec (rx1 (rect_of [t]))
                    (fst (sub_left_anchor sub))) as [HtLeft | HtReaches].
  - assert (HpLeft : fst p < fst (sub_left_anchor sub)).
    { assert (HpBox : in_segment_rect_or_endpoints t p).
      { apply segment_in_rect_or_endpoints. destruct Hp as [-> | ->];
          [apply onInit | apply onTerm]. }
      unfold in_segment_rect_or_endpoints, in_closed_rect in HpBox.
      destruct HpBox as [[_ Hpx] _]. lra. }
    pose proof (classify_up_has_up_path_invariant l sub r p Hctx Hup) as Hinv.
    eapply (ordinary_terminal_gate_blocks_left_certificate
              l sub r t p Hctx Hl HnotLid Ht Hover Hbelow Hp HtLeft).
    exact (proj1 (proj2 Hinv) HpLeft HpY).
  - pose proof (context_sub_nonempty l sub r Hctx) as Hsub.
    pose proof (context_sub_connected l sub r Hctx) as Hconn.
    pose proof (context_sub_x_monotone l sub r Hctx) as Hmono.
    destruct (x_monotone_rect_x_bounds sub Hsub Hconn Hmono)
      as [HsubLeft HsubRight].
    assert (HtAnchor :
        rx0 (rect_of [t]) <= fst (sub_left_anchor sub)
        <= rx1 (rect_of [t])).
    { unfold segment_x_ranges_overlap in Hover.
      destruct Hover as [HoverL _].
      change (Rmin (fst (init t)) (fst (term t)) <=
              fst (sub_left_anchor sub) <=
              Rmax (fst (init t)) (fst (term t))).
      change (Rmin (fst (init t)) (fst (term t)) <=
              Rmax (fst (init (last_segment l)))
                   (fst (term (last_segment l)))) in HoverL.
      rewrite Rmax_right in HoverL by lra.
      split.
      - now rewrite <- Hjoin.
      - exact (Rnot_lt_le _ _ HtReaches). }
    destruct (segment_has_point_at_x t (fst (sub_left_anchor sub)) HtAnchor)
      as [z [Hz Hzx]].
    assert (HleftOn : onSegmentlist sub (sub_left_anchor sub)).
    { unfold sub_left_anchor. exists (hd_segment sub). split.
      - destruct sub; [contradiction | now left].
      - apply onInit. }
    assert (HzRange : in_sub_x_range sub z).
    { unfold in_sub_x_range. rewrite Hzx, HsubLeft, HsubRight.
      unfold sub_left_anchor.
      pose proof (connected_x_monotone_endpoints sub Hsub Hconn Hmono).
      lra. }
    assert (HzBelow : below_sub_at_x sub z).
    { exists (sub_left_anchor sub). split; [exact HleftOn |].
      split; [exact Hzx |].
      pose proof (segment_in_rect_or_endpoints t z Hz) as HzBox.
        unfold in_segment_rect_or_endpoints, in_closed_rect in HzBox.
        destruct HzBox as [_ [_ Hzy1]].
        change (snd z <= Rmax (snd (init t)) (snd (term t))) in Hzy1.
        change (Rmax (snd (init t)) (snd (term t)) <
                Rmin (snd (init (last_segment l)))
                     (snd (term (last_segment l)))) in Hbelow.
        pose proof (Rmin_r (snd (init (last_segment l)))
                           (snd (term (last_segment l)))) as Hmin.
        assert (HzTerm : snd z < snd (term (last_segment l))) by lra.
        now rewrite Hjoin in HzTerm. }
    pose proof (nonadjacent_below_sub_point_classified_down
                  l sub r t p z Hctx Ht Hp Hz HzRange HzBelow).
    congruence.
Qed.

(* 右通常境界についての双対。 *)
Lemma classify_below_initial_not_up :
  forall l sub r,
    ClassificationContext l sub r ->
    r <> [] ->
    ~ initial_lid r ->
    forall t p,
      In t (nonadjacent_sides l r) ->
      segment_x_ranges_overlap t (hd_segment r) ->
      ry1 (rect_of [t]) < ry0 (rect_of [hd_segment r]) ->
      endpoint_of_seg t p ->
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
