Require Export Sparse.ReconnectSplit.
Require Import Stdlib.Logic.ClassicalDescription.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
Open Scope R_scope.
Lemma reconnect_one_endpoints_orn :
  forall l sub r h s,
    reconnectable_after l sub r h s ->
    init (reconnect_one l sub r h s) = operate_point l sub r h (init s)
    /\ term (reconnect_one l sub r h s) = operate_point l sub r h (term s)
    /\ orn_seg (reconnect_one l sub r h s) = orn_seg s.
Proof.
  intros l sub r h s Hrec. unfold reconnect_one.
  destruct (excluded_middle_informative
              (reconnectable_after l sub r h s)) as [H | H].
  - destruct (excluded_middle_informative
                (reconnect_slope_after l sub r h s)) as [Hs | Hs].
    + pose proof (make_seg_slope_spec _ _ _ _ _ Hs) as [Hi [Ht [Ho _]]].
      exact (conj Hi (conj Ht Ho)).
    + destruct (excluded_middle_informative
                  (head_init_slope_after l sub r h s)) as [Hi | Hi].
      * pose proof (make_seg_init_slope_spec
          _ _ _ _ (proj2 (proj2 Hi))) as [Hinit [Hterm [Horn _]]].
        exact (conj Hinit (conj Hterm Horn)).
      * destruct (excluded_middle_informative
                    (last_term_slope_after l sub r h s)) as [Ht | Ht].
        -- pose proof (make_seg_term_slope_spec
             _ _ _ _ (proj2 (proj2 Ht))) as [Hinit [Hterm [Horn _]]].
           exact (conj Hinit (conj Hterm Horn)).
        -- repeat split; [apply make_seg_init | apply make_seg_term | apply make_seg_orn].
  - contradiction.
Qed.

Lemma reconnect_one_init :
  forall l sub r h s,
    reconnectable_after l sub r h s ->
    init (reconnect_one l sub r h s) = operate_point l sub r h (init s).
Proof.
  intros l sub r h s Hrec.
  exact (proj1 (reconnect_one_endpoints_orn l sub r h s Hrec)).
Qed.

Lemma reconnect_one_term :
  forall l sub r h s,
    reconnectable_after l sub r h s ->
    term (reconnect_one l sub r h s) = operate_point l sub r h (term s).
Proof.
  intros l sub r h s Hrec.
  exact (proj1 (proj2 (reconnect_one_endpoints_orn l sub r h s Hrec))).
Qed.

Lemma reconnect_one_orn :
  forall l sub r h s,
    reconnectable_after l sub r h s ->
    orn_seg (reconnect_one l sub r h s) = orn_seg s.
Proof.
  intros l sub r h s Hrec.
  exact (proj2 (proj2 (reconnect_one_endpoints_orn l sub r h s Hrec))).
Qed.

Lemma reconnect_slope_after_init :
  forall l sub r h s,
    reconnect_slope_after l sub r h s ->
    reconnect_init_slope_after l sub r h s.
Proof.
  intros l sub r h s Hslope.
  unfold reconnect_slope_after, reconnect_init_slope_after,
    reconnect_init_slope.
  now exists (slope_term s).
Qed.

Lemma reconnect_slope_after_term :
  forall l sub r h s,
    reconnect_slope_after l sub r h s ->
    reconnect_term_slope_after l sub r h s.
Proof.
  intros l sub r h s Hslope.
  unfold reconnect_slope_after, reconnect_term_slope_after,
    reconnect_term_slope.
  now exists (slope_init s).
Qed.

(* 先頭として選ばれた再接続は、片側の存在条件だけで始点傾きを保存する。 *)
Lemma reconnect_one_head_slope_init :
  forall l sub r h s,
    l <> [] ->
    s = hd_segment l ->
    reconnect_init_slope_after l sub r h s ->
    slope_init (reconnect_one l sub r h s) = slope_init s.
Proof.
  intros l sub r h s Hl Hhead Hslope. unfold reconnect_one.
  destruct (excluded_middle_informative
              (reconnectable_after l sub r h s)) as [Hrec | Hrec].
  - destruct (excluded_middle_informative
                (reconnect_slope_after l sub r h s)) as [Hs | Hs].
    + exact (proj1 (proj2 (proj2 (proj2
        (make_seg_slope_spec _ _ _ _ _ Hs))))).
    + destruct (excluded_middle_informative
                  (head_init_slope_after l sub r h s)) as [Hi | Hi].
      * exact (proj2 (proj2 (proj2
          (make_seg_init_slope_spec _ _ _ _ (proj2 (proj2 Hi)))))).
      * exfalso. apply Hi. repeat split; assumption.
  - exfalso. apply Hrec. unfold reconnectable_after.
    unfold reconnect_init_slope_after in Hslope.
    now apply reconnect_init_slope_reconnectable with
      (slope_p := slope_init s).
Qed.

(* 先頭用分岐と競合しない末尾は、片側の存在条件だけで終点傾きを保存する。 *)
Lemma reconnect_one_last_slope_term :
  forall l sub r h s,
    ~ head_init_slope_after l sub r h s ->
    r <> [] ->
    s = last_segment r ->
    reconnect_term_slope_after l sub r h s ->
    slope_term (reconnect_one l sub r h s) = slope_term s.
Proof.
  intros l sub r h s HnotHead Hr Hlast Hslope. unfold reconnect_one.
  destruct (excluded_middle_informative
              (reconnectable_after l sub r h s)) as [Hrec | Hrec].
  - destruct (excluded_middle_informative
                (reconnect_slope_after l sub r h s)) as [Hs | Hs].
    + exact (proj2 (proj2 (proj2 (proj2
        (make_seg_slope_spec _ _ _ _ _ Hs))))).
    + destruct (excluded_middle_informative
                  (head_init_slope_after l sub r h s)) as [Hi | Hi].
      * contradiction.
      * destruct (excluded_middle_informative
                    (last_term_slope_after l sub r h s)) as [Ht | Ht].
        -- exact (proj2 (proj2 (proj2
            (make_seg_term_slope_spec _ _ _ _ (proj2 (proj2 Ht)))))).
        -- exfalso. apply Ht. repeat split; assumption.
  - exfalso. apply Hrec. unfold reconnectable_after.
    unfold reconnect_term_slope_after in Hslope.
    now apply reconnect_term_slope_reconnectable with
      (slope_q := slope_term s).
Qed.

(* 両端点が同じ領域なら、元のセグメントの平行移動が傾き付き再接続を与える。 *)
Lemma same_region_reconnect_slope_after :
  forall l sub r h s,
    classify l sub r (init s) = classify l sub r (term s) ->
    reconnect_slope_after l sub r h s.
Proof.
  intros l sub r h s Hregion. unfold reconnect_slope_after.
  apply (proj2 (reconnect_slope_spec _ _ _ _ _)).
  exists (translate_seg
            (region_translation h (classify l sub r (init s))) s).
  repeat split.
  - rewrite translate_seg_init. unfold operate_point.
    now rewrite shift_as_translation.
  - rewrite translate_seg_term. unfold operate_point.
    rewrite <- Hregion. now rewrite shift_as_translation.
  - apply translate_seg_orn.
  - apply translate_seg_slope_init.
  - apply translate_seg_slope_term.
Qed.

(* 始点を Up にする場合、終点の移動を差し引くと始点だけを上げる変形になる。 *)
Lemma raised_init_reconnect_slope_after :
  forall l sub r h seg,
    0 <= h ->
    classify l sub r (init seg) = RegUp ->
    (forall p,
      fst p = fst (init seg) ->
      snd (init seg) <= snd p ->
      reconnect_init_slope
        p (term seg) (orn_seg seg) (slope_init seg)) ->
    reconnect_init_slope_after l sub r h seg.
Proof.
  intros l sub r h seg Hh Hregion Hraise.
  set (g := classify l sub r (term seg)).
  set (v := region_translation h g).
  set (p0 := translate_pt (opposite_translation v)
               (shift h RegUp (init seg))).
  assert (Hx : fst p0 = fst (init seg)).
  { unfold p0, v, opposite_translation, translate_pt, region_translation,
      shift. destruct g; destruct (init seg); simpl; ring. }
  assert (Hy : snd (init seg) <= snd p0).
  { unfold p0, v, opposite_translation, translate_pt, region_translation,
      shift. destruct g; destruct (init seg); simpl; lra. }
  pose proof (Hraise p0 Hx Hy) as Hbase.
  pose proof (reconnect_init_slope_translate
                v p0 (term seg) (orn_seg seg) (slope_init seg) Hbase)
    as Htranslated.
  assert (Hp : translate_pt v p0 = shift h RegUp (init seg)).
  { unfold p0. apply translate_pt_opposite_left. }
  assert (Hq : translate_pt v (term seg) = shift h g (term seg)).
  { unfold v. symmetry. apply shift_as_translation. }
  unfold reconnect_init_slope_after, operate_point. rewrite Hregion.
  change (reconnect_init_slope
            (shift h RegUp (init seg)) (shift h g (term seg))
            (orn_seg seg) (slope_init seg)).
  now rewrite <- Hp, <- Hq.
Qed.

(* 始点を Down にする場合は、同様に始点だけを下げる変形へ帰着する。 *)
Lemma lowered_init_reconnect_slope_after :
  forall l sub r h seg,
    0 <= h ->
    classify l sub r (init seg) = RegDown ->
    (forall p,
      fst p = fst (init seg) ->
      snd p <= snd (init seg) ->
      reconnect_init_slope
        p (term seg) (orn_seg seg) (slope_init seg)) ->
    reconnect_init_slope_after l sub r h seg.
Proof.
  intros l sub r h seg Hh Hregion Hlower.
  set (g := classify l sub r (term seg)).
  set (v := region_translation h g).
  set (p0 := translate_pt (opposite_translation v)
               (shift h RegDown (init seg))).
  assert (Hx : fst p0 = fst (init seg)).
  { unfold p0, v, opposite_translation, translate_pt, region_translation,
      shift. destruct g; destruct (init seg); simpl; ring. }
  assert (Hy : snd p0 <= snd (init seg)).
  { unfold p0, v, opposite_translation, translate_pt, region_translation,
      shift. destruct g; destruct (init seg); simpl; lra. }
  pose proof (Hlower p0 Hx Hy) as Hbase.
  pose proof (reconnect_init_slope_translate
                v p0 (term seg) (orn_seg seg) (slope_init seg) Hbase)
    as Htranslated.
  assert (Hp : translate_pt v p0 = shift h RegDown (init seg)).
  { unfold p0. apply translate_pt_opposite_left. }
  assert (Hq : translate_pt v (term seg) = shift h g (term seg)).
  { unfold v. symmetry. apply shift_as_translation. }
  unfold reconnect_init_slope_after, operate_point. rewrite Hregion.
  change (reconnect_init_slope
            (shift h RegDown (init seg)) (shift h g (term seg))
            (orn_seg seg) (slope_init seg)).
  now rewrite <- Hp, <- Hq.
Qed.

(* 終点側についても、始点の移動を差し引いて片端変形へ帰着する。 *)
Lemma raised_term_reconnect_slope_after :
  forall l sub r h seg,
    0 <= h ->
    classify l sub r (term seg) = RegUp ->
    (forall p,
      fst p = fst (term seg) ->
      snd (term seg) <= snd p ->
      reconnect_term_slope
        (init seg) p (orn_seg seg) (slope_term seg)) ->
    reconnect_term_slope_after l sub r h seg.
Proof.
  intros l sub r h seg Hh Hregion Hraise.
  set (g := classify l sub r (init seg)).
  set (v := region_translation h g).
  set (q0 := translate_pt (opposite_translation v)
               (shift h RegUp (term seg))).
  assert (Hx : fst q0 = fst (term seg)).
  { unfold q0, v, opposite_translation, translate_pt, region_translation,
      shift. destruct g; destruct (term seg); simpl; ring. }
  assert (Hy : snd (term seg) <= snd q0).
  { unfold q0, v, opposite_translation, translate_pt, region_translation,
      shift. destruct g; destruct (term seg); simpl; lra. }
  pose proof (Hraise q0 Hx Hy) as Hbase.
  pose proof (reconnect_term_slope_translate
                v (init seg) q0 (orn_seg seg) (slope_term seg) Hbase)
    as Htranslated.
  assert (Hp : translate_pt v (init seg) = shift h g (init seg)).
  { unfold v. symmetry. apply shift_as_translation. }
  assert (Hq : translate_pt v q0 = shift h RegUp (term seg)).
  { unfold q0. apply translate_pt_opposite_left. }
  unfold reconnect_term_slope_after, operate_point. rewrite Hregion.
  change (reconnect_term_slope
            (shift h g (init seg)) (shift h RegUp (term seg))
            (orn_seg seg) (slope_term seg)).
  now rewrite <- Hp, <- Hq.
Qed.

Lemma lowered_term_reconnect_slope_after :
  forall l sub r h seg,
    0 <= h ->
    classify l sub r (term seg) = RegDown ->
    (forall p,
      fst p = fst (term seg) ->
      snd p <= snd (term seg) ->
      reconnect_term_slope
        (init seg) p (orn_seg seg) (slope_term seg)) ->
    reconnect_term_slope_after l sub r h seg.
Proof.
  intros l sub r h seg Hh Hregion Hlower.
  set (g := classify l sub r (init seg)).
  set (v := region_translation h g).
  set (q0 := translate_pt (opposite_translation v)
               (shift h RegDown (term seg))).
  assert (Hx : fst q0 = fst (term seg)).
  { unfold q0, v, opposite_translation, translate_pt, region_translation,
      shift. destruct g; destruct (term seg); simpl; ring. }
  assert (Hy : snd q0 <= snd (term seg)).
  { unfold q0, v, opposite_translation, translate_pt, region_translation,
      shift. destruct g; destruct (term seg); simpl; lra. }
  pose proof (Hlower q0 Hx Hy) as Hbase.
  pose proof (reconnect_term_slope_translate
                v (init seg) q0 (orn_seg seg) (slope_term seg) Hbase)
    as Htranslated.
  assert (Hp : translate_pt v (init seg) = shift h g (init seg)).
  { unfold v. symmetry. apply shift_as_translation. }
  assert (Hq : translate_pt v q0 = shift h RegDown (term seg)).
  { unfold q0. apply translate_pt_opposite_left. }
  unfold reconnect_term_slope_after, operate_point. rewrite Hregion.
  change (reconnect_term_slope
            (shift h g (init seg)) (shift h RegDown (term seg))
            (orn_seg seg) (slope_term seg)).
  now rewrite <- Hp, <- Hq.
Qed.

(* 東向きの sub に西向きから直接つながる先頭は、dc の水平反転二場合に限られる。 *)
Lemma singleton_head_before_x_monotone_sub_shape :
  forall ds seg sub r,
    sub <> [] ->
    x_monotone_segs sub ->
    embed_listDir ds ([seg] ++ sub ++ r) ->
    fst (init (hd_segment sub)) < fst (init seg) ->
    (embed (n, w, cc) seg /\ embed (n, e, cx) (hd_segment sub))
    \/ (embed (s, w, cx) seg /\ embed (s, e, cc) (hd_segment sub)).
Proof.
  intros ds s0 sub r Hne Hmono [sc [_ Hembed]] Hx.
  destruct sub as [|t sub']; [contradiction|].
  simpl in Hx |- *.
  assert (Hxt : x_monotone_seg t).
  { apply Hmono. now left. }
  destruct (embed_scurve_adjacent_data
              sc (s0 :: t :: sub' ++ r) 0 s0 t Hembed
              ltac:(reflexivity) ltac:(reflexivity))
    as [ps1 [ps2 [Hembed1 [Hembed2 [Hdc Hjoin]]]]].
  destruct Hdc; destruct h.
  - pose proof (e_end_relation s0 v c Hembed1).
    rewrite Hjoin in H. unfold x_monotone_seg, init_x, term_x in Hxt. lra.
  - pose proof (w_end_relation t v (i_c c) Hembed2).
    unfold x_monotone_seg, init_x, term_x in Hxt. lra.
  - pose proof (e_end_relation s0 n cx Hembed1).
    rewrite Hjoin in H. lra.
  - pose proof (w_end_relation t s cx Hembed2).
    unfold x_monotone_seg, init_x, term_x in Hxt. lra.
  - pose proof (e_end_relation s0 s cc Hembed1).
    rewrite Hjoin in H. lra.
  - pose proof (w_end_relation t n cc Hembed2).
    unfold x_monotone_seg, init_x, term_x in Hxt. lra.
  - pose proof (e_end_relation s0 n cc Hembed1).
    rewrite Hjoin in H. lra.
  - left. now split.
  - pose proof (e_end_relation s0 s cx Hembed1).
    rewrite Hjoin in H. lra.
  - right. now split.
Qed.

(* 東向きの sub から西向きへ直接つながる末尾も、dc の水平反転二場合に限られる。 *)
Lemma singleton_last_after_x_monotone_sub_shape :
  forall ds l sub seg,
    sub <> [] ->
    x_monotone_segs sub ->
    embed_listDir ds (l ++ sub ++ [seg]) ->
    fst (term seg) < fst (term (last_segment sub)) ->
    (embed (n, e, cc) (last_segment sub) /\ embed (n, w, cx) seg)
    \/ (embed (s, e, cx) (last_segment sub) /\ embed (s, w, cc) seg).
Proof.
  intros ds l sub s0 Hne Hmono [sc [_ Hembed]] Hx.
  assert (HsubPos : (0 < length sub)%nat).
  { destruct (length sub) eqn:Hlen; [|lia].
    apply length_zero_iff_nil in Hlen. contradiction. }
  set (i := (length l + length sub - 1)%nat).
  assert (HsubLast :
      nth_error (l ++ sub ++ [s0]) i = Some (last_segment sub)).
  { unfold i. rewrite nth_error_app2 by lia.
    replace (length l + length sub - 1 - length l)%nat
      with (length sub - 1)%nat by lia.
    rewrite nth_error_app1.
    - apply nth_error_last. exact Hne.
    - apply Nat.sub_lt; lia. }
  assert (Hs0 : nth_error (l ++ sub ++ [s0]) (S i) = Some s0).
  { unfold i. rewrite nth_error_app2 by lia.
    replace (S (length l + length sub - 1) - length l)%nat
      with (length sub)%nat by lia.
    rewrite nth_error_app2 by lia.
    now replace (length sub - length sub)%nat with 0%nat by lia. }
  destruct (embed_scurve_adjacent_data
              sc (l ++ sub ++ [s0]) i (last_segment sub) s0
              Hembed HsubLast Hs0)
    as [ps1 [ps2 [Hembed1 [Hembed2 [Hdc Hjoin]]]]].
  rewrite Hjoin in Hx.
  assert (Hxt : x_monotone_seg (last_segment sub)).
  { apply Hmono. apply last_In. exact Hne. }
  destruct Hdc; destruct h.
  - pose proof (e_end_relation s0 v (i_c c) Hembed2). lra.
  - pose proof (w_end_relation (last_segment sub) v c Hembed1).
    unfold x_monotone_seg, init_x, term_x in Hxt. lra.
  - pose proof (e_end_relation s0 s cx Hembed2). lra.
  - pose proof (w_end_relation (last_segment sub) n cx Hembed1).
    unfold x_monotone_seg, init_x, term_x in Hxt. lra.
  - pose proof (e_end_relation s0 n cc Hembed2). lra.
  - pose proof (w_end_relation (last_segment sub) s cc Hembed1).
    unfold x_monotone_seg, init_x, term_x in Hxt. lra.
  - left. now split.
  - pose proof (w_end_relation (last_segment sub) n cc Hembed1).
    unfold x_monotone_seg, init_x, term_x in Hxt. lra.
  - right. now split.
  - pose proof (w_end_relation (last_segment sub) s cx Hembed1).
    unfold x_monotone_seg, init_x, term_x in Hxt. lra.
Qed.

(* sub を挟む先頭と末尾は非隣接なので、疎性により同じセグメントではない。 *)
Lemma sparse_head_last_distinct_across_sub :
  forall l sub r,
    l <> [] -> sub <> [] -> r <> [] ->
    sparse_embedding (l ++ sub ++ r) ->
    hd_segment l <> last_segment r.
Proof.
  intros [|a l'] [|b sub'] [|c r'] Hl Hsub Hr Hsparse;
    try contradiction.
  simpl. intro Heq.
  destruct (Hsparse [] a (l' ++ b :: sub' ++ c :: r') ltac:(reflexivity))
    as [_ Hrect].
  assert (HinR : In (last_segment (c :: r')) (c :: r')).
  { apply last_In. discriminate. }
  assert (Hin :
      In (last_segment (c :: r'))
        (nonadjacent_sides [] (l' ++ b :: sub' ++ c :: r'))).
  { unfold nonadjacent_sides. simpl.
    destruct l' as [|d l'']; simpl.
    - apply in_or_app. right. exact HinR.
    - apply in_or_app. right. simpl. right.
      apply in_or_app. right. exact HinR. }
  specialize (Hrect (last_segment (c :: r')) (init a) Hin).
  apply Hrect.
  - rewrite <- Heq. now apply segment_in_rect_or_endpoints, onInit.
  - change (in_segment_rect_or_endpoints a (init a)).
    now apply segment_in_rect_or_endpoints, onInit.
Qed.

(* sub 側の端点だけを固定する先頭の特例では、延長線に必要な始点傾きだけを指定する。 *)
Lemma reconnect_head_fixed_endpoint_slope :
  forall ds l sub r h s,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    0 <= h ->
    l = [s] ->
    fst (init (hd_segment sub)) < fst (init s) ->
    reconnect_init_slope_after l sub r h (hd_segment l).
Proof.
  intros ds l sub r h s0 Hne Hconn Hmono Hsparse Hembed Hh Hl Hx.
  subst l. simpl in *.
  assert (Hwhole : connected ([s0] ++ sub ++ r)).
  { change (connected (s0 :: sub ++ r)).
    exact (embed_listDir_connected ds (s0 :: sub ++ r) Hembed). }
  assert (Hterm : term s0 = init (hd_segment sub)).
  { apply (embed_listDir_connected ds ([s0] ++ sub ++ r) Hembed 0%nat s0
             (hd_segment sub)); [reflexivity |].
    destruct sub; [contradiction | reflexivity]. }
  assert (HtermFix : classify [s0] sub r (term s0) = RegFix).
  { rewrite Hterm.
    exact (classified_sub_fixed
             [s0] sub r
             (classify_spec [s0] sub r Hne Hconn Hmono Hsparse Hwhole)
             (init (hd_segment sub))
             (onSegmentlist_init_hd sub Hne)). }
  destruct (singleton_head_before_x_monotone_sub_shape
              ds s0 sub r Hne Hmono Hembed Hx)
    as [[Hnorth _] | [Hsouth _]].
  - pose proof (n_end_relation s0 w cc Hnorth) as Hy.
    pose proof (proj1 (classified_segment_endpoints_monotone
                         [s0] sub r
                         (classify_spec [s0] sub r Hne Hconn Hmono Hsparse Hwhole)
                         s0 ltac:(simpl; auto)) Hy) as Horder.
    destruct (classify [s0] sub r (init s0)) eqn:HinitRegion.
    + apply reconnect_slope_after_init.
      apply same_region_reconnect_slope_after. now rewrite HtermFix.
    + rewrite HtermFix in Horder.
      destruct Horder as [Heq | Habove]; [discriminate | inversion Habove].
    + assert (Hlower :
          snd (shift h RegDown (init s0)) <= snd (init s0)).
      { destruct (init s0). simpl. lra. }
      unfold reconnect_init_slope_after, operate_point.
      rewrite HinitRegion, HtermFix. simpl.
      apply northwest_cc_lower_init_slope;
        [exact Hnorth | reflexivity | exact Hlower].
  - pose proof (s_end_relation s0 w cx Hsouth) as Hy.
    pose proof (proj2 (classified_segment_endpoints_monotone
                         [s0] sub r
                         (classify_spec [s0] sub r Hne Hconn Hmono Hsparse Hwhole)
                         s0 ltac:(simpl; auto)) Hy) as Horder.
    destruct (classify [s0] sub r (init s0)) eqn:HinitRegion.
    + apply reconnect_slope_after_init.
      apply same_region_reconnect_slope_after. now rewrite HtermFix.
    + assert (Hraise :
          snd (init s0) <= snd (shift h RegUp (init s0))).
      { destruct (init s0). simpl. lra. }
      unfold reconnect_init_slope_after, operate_point.
      rewrite HinitRegion, HtermFix. simpl.
      apply southwest_cx_raise_init_slope;
        [exact Hsouth | reflexivity | exact Hraise].
    + rewrite HtermFix in Horder.
      destruct Horder as [Heq | Habove]; [discriminate | inversion Habove].
Qed.

(* sub 側の端点だけを固定する末尾の特例。 *)
Lemma reconnect_last_fixed_endpoint_slope :
  forall ds l sub r h s,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    0 <= h ->
    r = [s] ->
    fst (term s) < fst (term (last_segment sub)) ->
    reconnect_term_slope_after l sub r h (last_segment r).
Proof.
  intros ds l sub r h s0 Hne Hconn Hmono Hsparse Hembed Hh Hr Hx.
  subst r. simpl in *.
  destruct Hembed as [sc [Hdir Hcurve]].
  assert (HembedList : embed_listDir ds (l ++ sub ++ [s0])).
  { exists sc. now split. }
  assert (Hwhole : connected (l ++ sub ++ [s0])).
  { exact (embed_listDir_connected ds (l ++ sub ++ [s0]) HembedList). }
  assert (Hinit : init s0 = term (last_segment sub)).
  { symmetry.
    assert (Hcurve' : embed_scurve sc ((l ++ sub) ++ [s0])).
    { rewrite <- app_assoc. exact Hcurve. }
    pose proof (consist_init_term
                  sc (l ++ sub) [s0] Hcurve'
                  ltac:(intro Hnil; apply app_eq_nil in Hnil as [_ Hsub]; contradiction)
                  ltac:(discriminate)) as Hjoin.
    simpl in Hjoin.
    change (term (last_segment (l ++ sub)) = init s0) in Hjoin.
    rewrite last_app_nonnil in Hjoin by exact Hne. exact Hjoin. }
  assert (HinitFix : classify l sub [s0] (init s0) = RegFix).
  { rewrite Hinit.
    exact (classified_sub_fixed
             l sub [s0]
             (classify_spec l sub [s0] Hne Hconn Hmono Hsparse Hwhole)
             (term (last_segment sub))
             (onSegmentlist_term_last sub Hne)). }
  destruct (singleton_last_after_x_monotone_sub_shape
              ds l sub s0 Hne Hmono HembedList Hx)
    as [[_ Hnorth] | [_ Hsouth]].
  - pose proof (n_end_relation s0 w cx Hnorth) as Hy.
    pose proof (proj1 (classified_segment_endpoints_monotone
                         l sub [s0]
                         (classify_spec l sub [s0] Hne Hconn Hmono Hsparse Hwhole)
                         s0 ltac:(rewrite !in_app_iff; simpl; auto)) Hy) as Horder.
    destruct (classify l sub [s0] (term s0)) eqn:HtermRegion.
    + apply reconnect_slope_after_term.
      apply same_region_reconnect_slope_after.
      change (classify l sub [s0] (init s0) =
              classify l sub [s0] (term s0)). congruence.
    + assert (Hraise :
          snd (term s0) <= snd (shift h RegUp (term s0))).
      { destruct (term s0). simpl. lra. }
      change (reconnect_term_slope
                (shift h (classify l sub [s0] (init s0)) (init s0))
                (shift h (classify l sub [s0] (term s0)) (term s0))
                (orn_seg s0) (slope_term s0)).
      rewrite HinitFix, HtermRegion. simpl.
      apply northwest_cx_raise_term_slope;
        [exact Hnorth | reflexivity | exact Hraise].
    + rewrite HinitFix in Horder.
      destruct Horder as [Heq | Habove]; [discriminate | inversion Habove].
  - pose proof (s_end_relation s0 w cc Hsouth) as Hy.
    pose proof (proj2 (classified_segment_endpoints_monotone
                         l sub [s0]
                         (classify_spec l sub [s0] Hne Hconn Hmono Hsparse Hwhole)
                         s0 ltac:(rewrite !in_app_iff; simpl; auto)) Hy) as Horder.
    destruct (classify l sub [s0] (term s0)) eqn:HtermRegion.
    + apply reconnect_slope_after_term.
      apply same_region_reconnect_slope_after.
      change (classify l sub [s0] (init s0) =
              classify l sub [s0] (term s0)). congruence.
    + rewrite HinitFix in Horder.
      destruct Horder as [Heq | Habove]; [discriminate | inversion Habove].
    + assert (Hlower :
          snd (shift h RegDown (term s0)) <= snd (term s0)).
      { destruct (term s0). simpl. lra. }
      change (reconnect_term_slope
                (shift h (classify l sub [s0] (init s0)) (init s0))
                (shift h (classify l sub [s0] (term s0)) (term s0))
                (orn_seg s0) (slope_term s0)).
      rewrite HinitFix, HtermRegion. simpl.
      apply southwest_cc_lower_term_slope;
        [exact Hsouth | reflexivity | exact Hlower].
Qed.

Lemma reconnect_head_init_slope_after :
  forall ds l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    0 <= h ->
    l <> [] ->
    reconnect_init_slope_after l sub r h (hd_segment l).
Proof.
  intros ds l sub r h Hne Hconn Hmono Hsparse Hembed Hh Hl.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  destruct (classified_head_slope_case
              l sub r
              (classify_spec l sub r Hne Hconn Hmono Hsparse Hwhole) Hl)
    as [Hsame | [[Hup [Hsw | Hse]] | [Hdown [Hnw | Hneast]]]].
  - apply reconnect_slope_after_init.
    now apply same_region_reconnect_slope_after.
  - eapply raised_init_reconnect_slope_after; [exact Hh | exact Hup |].
    intros p Hx Hy. now apply southwest_cx_raise_init_slope.
  - eapply raised_init_reconnect_slope_after; [exact Hh | exact Hup |].
    intros p Hx Hy. now apply southeast_cx_raise_init_slope.
  - eapply lowered_init_reconnect_slope_after; [exact Hh | exact Hdown |].
    intros p Hx Hy. now apply northwest_cc_lower_init_slope.
  - eapply lowered_init_reconnect_slope_after; [exact Hh | exact Hdown |].
    intros p Hx Hy. now apply northeast_cc_lower_init_slope.
Qed.

Lemma reconnect_last_term_slope_after :
  forall ds l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    0 <= h ->
    r <> [] ->
    reconnect_term_slope_after l sub r h (last_segment r).
Proof.
  intros ds l sub r h Hne Hconn Hmono Hsparse Hembed Hh Hr.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  destruct (classified_last_slope_case
              l sub r
              (classify_spec l sub r Hne Hconn Hmono Hsparse Hwhole) Hr)
    as [Hsame | [[Hup [Hnw | Hneast]] | [Hdown [Hsw | Hse]]]].
  - apply reconnect_slope_after_term.
    now apply same_region_reconnect_slope_after.
  - eapply raised_term_reconnect_slope_after; [exact Hh | exact Hup |].
    intros p Hx Hy. now apply northwest_cx_raise_term_slope.
  - eapply raised_term_reconnect_slope_after; [exact Hh | exact Hup |].
    intros p Hx Hy. now apply northeast_cx_raise_term_slope.
  - eapply lowered_term_reconnect_slope_after; [exact Hh | exact Hdown |].
    intros p Hx Hy. now apply southwest_cc_lower_term_slope.
  - eapply lowered_term_reconnect_slope_after; [exact Hh | exact Hdown |].
    intros p Hx Hy. now apply southeast_cc_lower_term_slope.
Qed.

(* 傾きを保存した再接続の始端延長線点を，移動前へ戻す。 *)
Lemma reconnect_one_head_extension_preimage :
  forall l sub r h s p,
    l <> [] ->
    s = hd_segment l ->
    reconnect_init_slope_after l sub r h s ->
    onHead (reconnect_one l sub r h s) p ->
    exists q,
      onHead s q
      /\ p = shift h (classify l sub r (init s)) q.
Proof.
  intros l sub r h s p Hl Hhead Hslope Hp.
  assert (Hrec : reconnectable_after l sub r h s).
  { unfold reconnectable_after.
    unfold reconnect_init_slope_after in Hslope.
    now apply reconnect_init_slope_reconnectable with
      (slope_p := slope_init s). }
  set (v := region_translation h (classify l sub r (init s))).
  assert (Hinit :
    init (reconnect_one l sub r h s) = init (translate_seg v s)).
  { rewrite reconnect_one_init by exact Hrec.
    rewrite translate_seg_init. unfold operate_point, v.
    now rewrite shift_as_translation. }
  assert (HslopeEq :
    slope_init (reconnect_one l sub r h s) =
    slope_init (translate_seg v s)).
  { rewrite (reconnect_one_head_slope_init _ _ _ _ _ Hl Hhead Hslope).
    symmetry. apply translate_seg_slope_init. }
  pose proof (proj1
    (head_extension_determined_by_init_slope
       (reconnect_one l sub r h s) (translate_seg v s)
       Hinit HslopeEq p) Hp) as Htranslated.
  destruct Htranslated as [t [Ht Hpoint]].
  exists (point s t). split.
  - exists t. split; [exact Ht | reflexivity].
  - rewrite shift_as_translation. unfold v in Hpoint.
    rewrite translate_seg_point in Hpoint. simpl in Hpoint.
    symmetry. exact Hpoint.
Qed.

(* 傾き保存した再接続の終端延長線点の移動前の像。 *)
Lemma reconnect_one_last_extension_preimage :
  forall l sub r h s p,
    ~ head_init_slope_after l sub r h s ->
    r <> [] ->
    s = last_segment r ->
    reconnect_term_slope_after l sub r h s ->
    onLast (reconnect_one l sub r h s) p ->
    exists q,
      onLast s q
      /\ p = shift h (classify l sub r (term s)) q.
Proof.
  intros l sub r h s p HnotHead Hr Hlast Hslope Hp.
  assert (Hrec : reconnectable_after l sub r h s).
  { unfold reconnectable_after.
    unfold reconnect_term_slope_after in Hslope.
    now apply reconnect_term_slope_reconnectable with
      (slope_q := slope_term s). }
  set (v := region_translation h (classify l sub r (term s))).
  assert (Hterm :
    term (reconnect_one l sub r h s) = term (translate_seg v s)).
  { rewrite reconnect_one_term by exact Hrec.
    rewrite translate_seg_term. unfold operate_point, v.
    now rewrite shift_as_translation. }
  assert (HslopeEq :
    slope_term (reconnect_one l sub r h s) =
    slope_term (translate_seg v s)).
  { rewrite (reconnect_one_last_slope_term
               _ _ _ _ _ HnotHead Hr Hlast Hslope).
    symmetry. apply translate_seg_slope_term. }
  pose proof (proj1
    (last_extension_determined_by_term_slope
       (reconnect_one l sub r h s) (translate_seg v s)
       Hterm HslopeEq p) Hp) as Htranslated.
  destruct Htranslated as [t [Ht Hpoint]].
  exists (point s t). split.
  - exists t. split; [exact Ht | reflexivity].
  - rewrite shift_as_translation. unfold v in Hpoint.
    rewrite translate_seg_point in Hpoint. simpl in Hpoint.
    symmetry. exact Hpoint.
Qed.

(* 再接続後の先頭延長線は，旧先頭延長線の一律な上下移動である。 *)
Lemma reconnect_head_extension_preimage :
  forall l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (l <> [] -> reconnect_init_slope_after l sub r h (hd_segment l)) ->
    onHead_extend (reconnect_split l sub r h) p ->
    exists q,
      onHead_extend (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (init (hd_segment (l ++ sub ++ r)))) q.
Proof.
  intros l sub r h p Hne Hconn Hmono Hsparse Hwhole Hslope Hp.
  destruct l as [|a l'].
  - destruct sub as [|b sub']; [contradiction|].
    assert (Hfix : classify [] (b :: sub') r (init b) = RegFix).
    { apply (classified_sub_fixed
               [] (b :: sub') r
               (classify_spec [] (b :: sub') r
                  ltac:(discriminate) Hconn Hmono Hsparse Hwhole)).
      apply onSegmentlist_init_hd. discriminate. }
    exists p. split.
    + exact Hp.
    + simpl in Hfix |- *. now rewrite Hfix.
  - simpl in Hp |- *.
    apply (reconnect_one_head_extension_preimage
             (a :: l') sub r h a p).
    + discriminate.
    + reflexivity.
    + now apply Hslope; discriminate.
    + exact Hp.
Qed.

(* 再接続後の末尾延長線の移動前の像。 *)
Lemma reconnect_last_extension_preimage :
  forall l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (r <> [] -> reconnect_term_slope_after l sub r h (last_segment r)) ->
    onLast_extend (reconnect_split l sub r h) p ->
    exists q,
      onLast_extend (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (term (last_segment (l ++ sub ++ r)))) q.
Proof.
  intros l sub r h p Hne Hconn Hmono Hsparse Hwhole Hslope Hp.
  destruct r as [|a r'].
  - assert (HoldLast : last_segment (l ++ sub ++ []) = last_segment sub).
    { rewrite app_nil_r. apply last_app_nonnil. exact Hne. }
    assert (HnewLast :
      last_segment (reconnect_split l sub [] h) = last_segment sub).
    { unfold reconnect_split, reconnect_segs. simpl. rewrite app_nil_r.
      apply last_app_nonnil. exact Hne. }
    assert (Hfix : classify l sub [] (term (last_segment sub)) = RegFix).
    { apply (classified_sub_fixed
               l sub []
               (classify_spec l sub [] Hne Hconn Hmono Hsparse Hwhole)).
      apply onSegmentlist_term_last. exact Hne. }
    exists p. split.
    + unfold onLast_extend in *. now rewrite HnewLast in Hp; rewrite HoldLast.
    + rewrite HoldLast, Hfix. reflexivity.
  - assert (HoldLast :
      last_segment (l ++ sub ++ a :: r') = last_segment (a :: r')).
    { assert (Htail : sub ++ a :: r' <> []) by
        (destruct sub; discriminate).
      rewrite (last_app_nonnil l (sub ++ a :: r')) by exact Htail.
      apply last_app_nonnil. discriminate. }
    assert (HnewLast :
      last_segment (reconnect_split l sub (a :: r') h) =
      reconnect_one l sub (a :: r') h (last_segment (a :: r'))).
    { unfold reconnect_split, reconnect_segs.
      assert (Hmap : map (reconnect_one l sub (a :: r') h) (a :: r') <> [])
        by discriminate.
      assert (Htail :
        sub ++ map (reconnect_one l sub (a :: r') h) (a :: r') <> []) by
        (destruct sub; discriminate).
      rewrite (last_app_nonnil
                 (map (reconnect_one l sub (a :: r') h) l)
                 (sub ++ map (reconnect_one l sub (a :: r') h) (a :: r')))
        by exact Htail.
      rewrite (last_app_nonnil sub
                 (map (reconnect_one l sub (a :: r') h) (a :: r')))
        by exact Hmap.
      apply last_map_nonnil. discriminate. }
    unfold onLast_extend in Hp |- *.
    rewrite HnewLast in Hp. rewrite HoldLast.
    apply (reconnect_one_last_extension_preimage
             l sub (a :: r') h (last_segment (a :: r')) p).
    + unfold head_init_slope_after. intros [Hl [Heq _]].
      pose proof (sparse_head_last_distinct_across_sub
                    l sub (a :: r') Hl Hne ltac:(discriminate) Hsparse)
        as Hdistinct.
      apply Hdistinct. now symmetry.
    + discriminate.
    + reflexivity.
    + now apply Hslope; discriminate.
    + exact Hp.
Qed.

(* 再接続後の strict 先頭延長線点は，移動前の strict
   延長線点を先頭の分類どおりに動かしたものである。 *)
Lemma reconnect_head_strict_extension_preimage :
  forall ds l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    0 <= h ->
    onHead_extend_strict (reconnect_split l sub r h) p ->
    exists q,
      onHead_extend_strict (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (init (hd_segment (l ++ sub ++ r)))) q.
Proof.
  intros ds l sub r h p Hne Hconn Hmono Hsparse Hembed Hh Hstrict.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  destruct l as [|a l'].
  - destruct sub as [|b sub']; [contradiction|].
    assert (Hfix : classify [] (b :: sub') r (init b) = RegFix).
    { apply (classified_sub_fixed
               [] (b :: sub') r
               (classify_spec [] (b :: sub') r
                  ltac:(discriminate) Hconn Hmono Hsparse Hwhole)).
      apply onSegmentlist_init_hd. discriminate. }
    exists p. split.
    + exact Hstrict.
    + simpl in Hfix |- *. now rewrite Hfix.
  - simpl in Hstrict |- *.
    destruct Hstrict as [t [Ht Hpoint]].
    change (point (reconnect_one (a :: l') sub r h a) t = p) in Hpoint.
    pose proof (reconnect_head_init_slope_after
                  ds (a :: l') sub r h Hne Hconn Hmono Hsparse Hembed Hh
                  ltac:(discriminate)) as Hslope.
    simpl in Hslope.
    assert (Hrec : reconnectable_after (a :: l') sub r h a).
    { unfold reconnectable_after.
      unfold reconnect_init_slope_after in Hslope.
      now apply reconnect_init_slope_reconnectable with
        (slope_p := slope_init a). }
    set (v := region_translation h
                (classify (a :: l') sub r (init a))).
    assert (Hinit :
      init (reconnect_one (a :: l') sub r h a) =
      init (translate_seg v a)).
    { rewrite reconnect_one_init by exact Hrec.
      rewrite translate_seg_init. unfold operate_point, v.
      now rewrite shift_as_translation. }
    assert (HslopeEq :
      slope_init (reconnect_one (a :: l') sub r h a) =
      slope_init (translate_seg v a)).
    { rewrite (reconnect_one_head_slope_init
                 (a :: l') sub r h a ltac:(discriminate)
                 ltac:(reflexivity) Hslope).
      symmetry. apply translate_seg_slope_init. }
    assert (HonNew : onHead (reconnect_one (a :: l') sub r h a) p).
    { exists t. split; [lra | exact Hpoint]. }
    pose proof (proj1
      (head_extension_determined_by_init_slope
         (reconnect_one (a :: l') sub r h a)
         (translate_seg v a) Hinit HslopeEq p) HonNew) as HonTranslated.
    destruct HonTranslated as [u [Hu Htranslated]].
    assert (HuStrict : u < 0).
    { destruct (Req_dec u 0) as [Hu0 | Hu0]; [|lra].
      subst u.
      assert (Ht0 : t = 0).
      { apply (point_injective (reconnect_one (a :: l') sub r h a)).
        rewrite Hpoint.
        change (p = init (reconnect_one (a :: l') sub r h a)).
        rewrite Hinit.
        change (p = point (translate_seg v a) 0).
        symmetry. exact Htranslated. }
      lra. }
    exists (point a u). split.
    + exists u. split; [exact HuStrict | reflexivity].
    + rewrite shift_as_translation. unfold v in Htranslated.
      rewrite translate_seg_point in Htranslated. simpl in Htranslated.
      symmetry. exact Htranslated.
Qed.

(* 再接続後の strict 末尾延長線点の移動前の像。 *)
Lemma reconnect_last_strict_extension_preimage :
  forall ds l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    0 <= h ->
    onLast_extend_strict (reconnect_split l sub r h) p ->
    exists q,
      onLast_extend_strict (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (term (last_segment (l ++ sub ++ r)))) q.
Proof.
  intros ds l sub r h p Hne Hconn Hmono Hsparse Hembed Hh Hstrict.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  destruct r as [|a r'].
  - assert (HoldLast : last_segment (l ++ sub ++ []) = last_segment sub).
    { rewrite app_nil_r. apply last_app_nonnil. exact Hne. }
    assert (HnewLast :
      last_segment (reconnect_split l sub [] h) = last_segment sub).
    { unfold reconnect_split, reconnect_segs. simpl. rewrite app_nil_r.
      apply last_app_nonnil. exact Hne. }
    assert (Hfix : classify l sub [] (term (last_segment sub)) = RegFix).
    { apply (classified_sub_fixed
               l sub []
               (classify_spec l sub [] Hne Hconn Hmono Hsparse Hwhole)).
      apply onSegmentlist_term_last. exact Hne. }
    exists p. split.
    + unfold onLast_extend_strict in *. now rewrite HnewLast in Hstrict;
        rewrite HoldLast.
    + rewrite HoldLast, Hfix. reflexivity.
  - assert (HoldLast :
      last_segment (l ++ sub ++ a :: r') = last_segment (a :: r')).
    { assert (Htail : sub ++ a :: r' <> []).
      { destruct sub; discriminate. }
      rewrite (last_app_nonnil l (sub ++ a :: r')) by exact Htail.
      apply last_app_nonnil. discriminate. }
    assert (HnewLast :
      last_segment (reconnect_split l sub (a :: r') h) =
      reconnect_one l sub (a :: r') h (last_segment (a :: r'))).
    { unfold reconnect_split, reconnect_segs.
      assert (Hmap : map (reconnect_one l sub (a :: r') h) (a :: r') <> [])
        by discriminate.
      assert (Htail :
        sub ++ map (reconnect_one l sub (a :: r') h) (a :: r') <> []).
      { destruct sub; discriminate. }
      rewrite (last_app_nonnil
                 (map (reconnect_one l sub (a :: r') h) l)
                 (sub ++ map (reconnect_one l sub (a :: r') h) (a :: r')))
        by exact Htail.
      rewrite (last_app_nonnil sub
                 (map (reconnect_one l sub (a :: r') h) (a :: r')))
        by exact Hmap.
      apply last_map_nonnil. discriminate. }
    unfold onLast_extend_strict in Hstrict.
    rewrite HnewLast in Hstrict.
    destruct Hstrict as [t [Ht Hpoint]].
    pose proof (reconnect_last_term_slope_after
                  ds l sub (a :: r') h Hne Hconn Hmono Hsparse Hembed Hh
                  ltac:(discriminate)) as Hslope.
    set (s := last_segment (a :: r')).
    change (reconnect_term_slope_after l sub (a :: r') h s) in Hslope.
    change (point (reconnect_one l sub (a :: r') h s) t = p) in Hpoint.
    assert (Hrec : reconnectable_after l sub (a :: r') h s).
    { unfold reconnectable_after.
      unfold reconnect_term_slope_after in Hslope.
      now apply reconnect_term_slope_reconnectable with
        (slope_q := slope_term s). }
    assert (HnotHead : ~ head_init_slope_after l sub (a :: r') h s).
    { unfold head_init_slope_after. intros [Hl [Heq _]].
      pose proof (sparse_head_last_distinct_across_sub
                    l sub (a :: r') Hl Hne ltac:(discriminate) Hsparse)
        as Hdistinct.
      apply Hdistinct. unfold s in Heq. now symmetry. }
    set (v := region_translation h (classify l sub (a :: r') (term s))).
    assert (Hterm :
      term (reconnect_one l sub (a :: r') h s) =
      term (translate_seg v s)).
    { rewrite reconnect_one_term by exact Hrec.
      rewrite translate_seg_term. unfold operate_point, v.
      now rewrite shift_as_translation. }
    assert (HslopeEq :
      slope_term (reconnect_one l sub (a :: r') h s) =
      slope_term (translate_seg v s)).
    { rewrite (reconnect_one_last_slope_term
                 _ _ _ _ _ HnotHead ltac:(discriminate)
                 ltac:(reflexivity) Hslope).
      symmetry. apply translate_seg_slope_term. }
    assert (HonNew : onLast (reconnect_one l sub (a :: r') h s) p).
    { exists t. split; [lra | exact Hpoint]. }
    pose proof (proj1
      (last_extension_determined_by_term_slope
         (reconnect_one l sub (a :: r') h s)
         (translate_seg v s) Hterm HslopeEq p) HonNew) as HonTranslated.
    destruct HonTranslated as [u [Hu Htranslated]].
    assert (HuStrict : 1 < u).
    { destruct (Req_dec u 1) as [Hu1 | Hu1]; [|lra].
      subst u.
      assert (Ht1 : t = 1).
      { apply (point_injective (reconnect_one l sub (a :: r') h s)).
        rewrite Hpoint.
        change (p = term (reconnect_one l sub (a :: r') h s)).
        rewrite Hterm.
        change (p = point (translate_seg v s) 1).
        symmetry. exact Htranslated. }
      lra. }
    exists (point s u). split.
    + unfold onLast_extend_strict. rewrite HoldLast.
      change (exists u0, 1 < u0 /\ point s u0 = point s u).
      exists u. split; [exact HuStrict | reflexivity].
    + rewrite HoldLast. change (p = shift h (classify l sub (a :: r') (term s)) (point s u)).
      rewrite shift_as_translation. unfold v in Htranslated.
      rewrite translate_seg_point in Htranslated. simpl in Htranslated.
      symmetry. exact Htranslated.
Qed.

Lemma all_reconnectable_mono :
  forall l sub r h ls ls',
    all_reconnectable l sub r h ls ->
    (forall s, In s ls' -> In s ls) ->
    all_reconnectable l sub r h ls'.
Proof.
  intros l sub r h ls ls' Hrec Hin s Hs. apply Hrec, Hin, Hs.
Qed.

Lemma reconnect_segs_length :
  forall l sub r h ls,
    length (reconnect_segs l sub r h ls) = length ls.
Proof. intros. unfold reconnect_segs. apply length_map. Qed.

Lemma reconnect_segs_nth_error :
  forall l sub r h ls i s,
    nth_error ls i = Some s ->
    nth_error (reconnect_segs l sub r h ls) i =
      Some (reconnect_one l sub r h s).
Proof.
  intros l sub r h ls i s H. unfold reconnect_segs.
  rewrite nth_error_map, H. reflexivity.
Qed.

(* 同じ端点に同じ classify を適用するため、各部分列内部の連結性は保たれる。 *)
Lemma reconnect_segs_connected :
  forall l sub r h ls,
    all_reconnectable l sub r h ls ->
    connected ls ->
    connected (reconnect_segs l sub r h ls).
Proof.
  intros l sub r h ls Hrec Hc i s1 s2 H1 H2.
  unfold reconnect_segs in H1, H2.
  destruct (nth_error_map_inv _ _ _ _ H1) as [a [Ha Ea]].
  destruct (nth_error_map_inv _ _ _ _ H2) as [b [Hb Eb]].
  subst s1 s2.
  rewrite reconnect_one_term, reconnect_one_init.
  2,3: apply Hrec; eapply nth_error_In; eauto.
  f_equal. exact (Hc i a b Ha Hb).
Qed.

(* 再接続は各セグメントの向きと列の連結性を保つ。 *)
Lemma reconnect_preserves_embed :
  forall l sub r h ds ls,
    all_reconnectable l sub r h ls ->
    embed_listDir ds ls ->
    embed_listDir ds (reconnect_segs l sub r h ls).
Proof.
  intros l sub r h ds ls Hrec Hemb.
  eapply embed_scurve_transfer; [exact Hemb | | |].
  - apply reconnect_segs_length.
  - intros i s s' Hs Hs'.
    rewrite (reconnect_segs_nth_error l sub r h ls i s Hs) in Hs'.
    injection Hs' as Hs'. subst s'.
    apply reconnect_one_orn, Hrec. eapply nth_error_In; exact Hs.
  - eapply reconnect_segs_connected; [exact Hrec |].
    eapply embed_listDir_connected; exact Hemb.
Qed.
