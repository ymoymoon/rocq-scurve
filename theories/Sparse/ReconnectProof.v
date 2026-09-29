Require Export Sparse.ReconnectSplit.
Require Import Stdlib.Logic.ClassicalDescription.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.

(* x 方向が反転する隣接セグメントの向きを [dc] から取り出す。 *)
Lemma west_to_east_dc_shapes :
  forall seg1 seg2 ps1 ps2,
    embed ps1 seg1 ->
    embed ps2 seg2 ->
    dc ps1 ps2 ->
    fst (term seg1) < fst (init seg1) ->
    fst (init seg2) < fst (term seg2) ->
    (embed (n, w, cc) seg1 \/ embed (s, w, cx) seg1)
    /\ (embed (n, e, cx) seg2 \/ embed (s, e, cc) seg2).
Proof.
  intros seg1 seg2 ps1 ps2 Hemb1 Hemb2 Hdc Hwest Heast.
  destruct Hdc; destruct h.
  - exfalso. pose proof (e_end_relation seg1 v c Hemb1). lra.
  - exfalso. pose proof (w_end_relation seg2 v (i_c c) Hemb2). lra.
  - exfalso. pose proof (e_end_relation seg1 n cx Hemb1). lra.
  - exfalso. pose proof (w_end_relation seg2 s cx Hemb2). lra.
  - exfalso. pose proof (e_end_relation seg1 s cc Hemb1). lra.
  - exfalso. pose proof (w_end_relation seg2 n cc Hemb2). lra.
  - exfalso. pose proof (e_end_relation seg1 n cc Hemb1). lra.
  - split; [now left | now left].
  - exfalso. pose proof (e_end_relation seg1 s cx Hemb1). lra.
  - split; [now right | now right].
Qed.

Lemma east_to_west_dc_shapes :
  forall seg1 seg2 ps1 ps2,
    embed ps1 seg1 ->
    embed ps2 seg2 ->
    dc ps1 ps2 ->
    fst (init seg1) < fst (term seg1) ->
    fst (term seg2) < fst (init seg2) ->
    (embed (n, e, cc) seg1 \/ embed (s, e, cx) seg1)
    /\ (embed (n, w, cx) seg2 \/ embed (s, w, cc) seg2).
Proof.
  intros seg1 seg2 ps1 ps2 Hemb1 Hemb2 Hdc Heast Hwest.
  destruct Hdc; destruct h.
  - exfalso. pose proof (e_end_relation seg2 v (i_c c) Hemb2). lra.
  - exfalso. pose proof (w_end_relation seg1 v c Hemb1). lra.
  - exfalso. pose proof (e_end_relation seg2 s cx Hemb2). lra.
  - exfalso. pose proof (w_end_relation seg1 n cx Hemb1). lra.
  - exfalso. pose proof (e_end_relation seg2 n cc Hemb2). lra.
  - exfalso. pose proof (w_end_relation seg1 s cc Hemb1). lra.
  - split; [now left | now left].
  - exfalso. pose proof (w_end_relation seg1 n cc Hemb1). lra.
  - split; [now right | now right].
  - exfalso. pose proof (w_end_relation seg1 s cx Hemb1). lra.
Qed.

(* 埋め込み列を二つに分けた境界では、左右の末尾・先頭に対応する
   PrimitiveSegment とその [dc] 証明を取り出せる。 *)
Lemma embed_listDir_app_boundary_data :
  forall ds left right,
    left <> [] ->
    right <> [] ->
    embed_listDir ds (left ++ right) ->
    exists ps1 ps2,
      embed ps1 (last_segment left)
      /\ embed ps2 (hd_segment right)
      /\ dc ps1 ps2
      /\ term (last_segment left) = init (hd_segment right).
Proof.
  intros ds left right Hleft Hright [sc [_ Hembed]].
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
      now repeat split.
    + destruct (excluded_middle_informative
                  (head_init_slope_after l sub r h s)) as [Hi | Hi].
      * pose proof (make_seg_init_slope_spec
          _ _ _ _ (proj2 (proj2 Hi))) as [Hinit [Hterm [Horn _]]].
        now repeat split.
      * destruct (excluded_middle_informative
                    (last_term_slope_after l sub r h s)) as [Ht | Ht].
        -- pose proof (make_seg_term_slope_spec
             _ _ _ _ (proj2 (proj2 Ht))) as [Hinit [Hterm [Horn _]]].
           now repeat split.
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

Require Export Sparse.Classify.

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
    rewrite translate_seg_init. unfold operate_point.
    exact (shift_as_translation h (classify l sub r (init s)) (init s)). }
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
    rewrite translate_seg_term. unfold operate_point.
    exact (shift_as_translation h (classify l sub r (term s)) (term s)). }
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
Lemma reconnect_head_extension_preimage_from_spec :
  forall l sub r h p,
    sub <> [] ->
    @ClassificationSpec l sub r (classify l sub r) ->
    (l <> [] -> reconnect_init_slope_after l sub r h (hd_segment l)) ->
    onHead_extend (ordinary_reconnect_split l sub r h) p ->
    exists q,
      onHead_extend (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (init (hd_segment (l ++ sub ++ r)))) q.
Proof.
  intros l sub r h p Hne Hspec Hslope Hp.
  destruct l as [|a l'].
  - destruct sub as [|b sub']; [contradiction|].
    assert (Hfix : classify [] (b :: sub') r (init b) = RegFix).
    { apply (classified_sub_fixed [] (b :: sub') r Hspec).
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
Lemma reconnect_last_extension_preimage_from_spec :
  forall l sub r h p,
    sub <> [] ->
    @ClassificationSpec l sub r (classify l sub r) ->
    sparse_embedding (l ++ sub ++ r) ->
    (r <> [] -> reconnect_term_slope_after l sub r h (last_segment r)) ->
    onLast_extend (ordinary_reconnect_split l sub r h) p ->
    exists q,
      onLast_extend (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (term (last_segment (l ++ sub ++ r)))) q.
Proof.
  intros l sub r h p Hne Hspec Hsparse Hslope Hp.
  destruct r as [|a r'].
  - assert (HoldLast : last_segment (l ++ sub ++ []) = last_segment sub).
    { rewrite app_nil_r. apply last_app_nonnil. exact Hne. }
    assert (HnewLast :
      last_segment (ordinary_reconnect_split l sub [] h) = last_segment sub).
    { unfold ordinary_reconnect_split, reconnect_segs. simpl. rewrite app_nil_r.
      apply last_app_nonnil. exact Hne. }
    assert (Hfix : classify l sub [] (term (last_segment sub)) = RegFix).
    { apply (classified_sub_fixed l sub [] Hspec).
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
      last_segment (ordinary_reconnect_split l sub (a :: r') h) =
      reconnect_one l sub (a :: r') h (last_segment (a :: r'))).
    { unfold ordinary_reconnect_split, reconnect_segs.
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
Lemma reconnect_head_strict_extension_preimage_from_spec :
  forall l sub r h p,
    sub <> [] ->
    sparse_embedding (l ++ sub ++ r) ->
    @ClassificationSpec l sub r (classify l sub r) ->
    0 <= h ->
    onHead_extend_strict (ordinary_reconnect_split l sub r h) p ->
    exists q,
      onHead_extend_strict (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (init (hd_segment (l ++ sub ++ r)))) q.
Proof.
  intros l sub r h p Hne Hsparse Hspec Hh Hstrict.
  destruct l as [|a l'].
  - destruct sub as [|b sub']; [contradiction|].
    assert (Hfix : classify [] (b :: sub') r (init b) = RegFix).
    { apply (classified_sub_fixed [] (b :: sub') r Hspec).
      apply onSegmentlist_init_hd. discriminate. }
    exists p. split.
    + exact Hstrict.
    + simpl in Hfix |- *. now rewrite Hfix.
  - simpl in Hstrict |- *.
    destruct Hstrict as [t [Ht Hpoint]].
    change (point (reconnect_one (a :: l') sub r h a) t = p) in Hpoint.
    pose proof (classified_head_init_slope_reconnectable
                  (a :: l') sub r Hspec h Hh ltac:(discriminate))
      as Hslope.
    change (reconnect_init_slope_after (a :: l') sub r h a) in Hslope.
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
      rewrite translate_seg_init. unfold operate_point.
      exact (shift_as_translation h
        (classify (a :: l') sub r (init a)) (init a)). }
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
Lemma reconnect_last_strict_extension_preimage_from_spec :
  forall l sub r h p,
    sub <> [] ->
    sparse_embedding (l ++ sub ++ r) ->
    @ClassificationSpec l sub r (classify l sub r) ->
    0 <= h ->
    onLast_extend_strict (ordinary_reconnect_split l sub r h) p ->
    exists q,
      onLast_extend_strict (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (term (last_segment (l ++ sub ++ r)))) q.
Proof.
  intros l sub r h p Hne Hsparse Hspec Hh Hstrict.
  destruct r as [|a r'].
  - assert (HoldLast : last_segment (l ++ sub ++ []) = last_segment sub).
    { rewrite app_nil_r. apply last_app_nonnil. exact Hne. }
    assert (HnewLast :
      last_segment (ordinary_reconnect_split l sub [] h) = last_segment sub).
    { unfold ordinary_reconnect_split, reconnect_segs. simpl. rewrite app_nil_r.
      apply last_app_nonnil. exact Hne. }
    assert (Hfix : classify l sub [] (term (last_segment sub)) = RegFix).
    { apply (classified_sub_fixed l sub [] Hspec).
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
      last_segment (ordinary_reconnect_split l sub (a :: r') h) =
      reconnect_one l sub (a :: r') h (last_segment (a :: r'))).
    { unfold ordinary_reconnect_split, reconnect_segs.
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
    pose proof (classified_last_term_slope_reconnectable
                  l sub (a :: r') Hspec h Hh ltac:(discriminate))
      as Hslope.
    set (s := last_segment (a :: r')).
    change (reconnect_term_slope_after l sub (a :: r') h s) in Hslope.
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
      rewrite translate_seg_term. unfold operate_point.
      exact (shift_as_translation h
        (classify l sub (a :: r') (term s)) (term s)). }
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

Lemma reconnect_segs_length :
  forall l sub r h ls,
    length (reconnect_segs l sub r h ls) = length ls.
Proof. intros. unfold reconnect_segs. apply length_map. Qed.

(* map による再接続列は、各位置で分類後の端点と元の向きを共有する。 *)
Lemma reconnect_segs_reconnects_after :
  forall l sub r h ls,
    all_reconnectable l sub r h ls ->
    reconnects_list_after l sub r h ls (reconnect_segs l sub r h ls).
Proof.
  intros l sub r h ls Hrec.
  unfold reconnects_list_after.
  induction ls as [|s ls IH]; simpl.
  - constructor.
  - constructor.
    + unfold reconnects_after.
      exact (reconnect_one_endpoints_orn l sub r h s (Hrec s (or_introl eq_refl))).
    + apply IH. intros t Ht. apply Hrec. now right.
Qed.

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

(* sub に隣接する l 末尾より下の端点は、分類移動後にもその旧長方形
   より下に残る。隣接・非隣接の区別は不要である。 *)

Lemma operated_endpoint_below_terminal_stays_below_from_spec :
  forall l sub r h p,
    @ClassificationSpec l sub r (classify l sub r) ->
    0 <= h ->
    l <> [] ->
    ~ terminal_lid l ->
    endpoint_of (l ++ sub ++ r) p ->
    snd p < ry0 (rect_of [last_segment l]) ->
    snd (operate_point l sub r h p) < ry0 (rect_of [last_segment l]).
Proof.
  intros l sub r h p Hspec Hh Hl HnotLid Hp Hbelow.
  unfold operate_point.
  pose proof (classified_below_terminal_not_up
                l sub r Hspec Hl HnotLid p Hp Hbelow) as HnotUp.
  pose proof (shift_not_up_nonincreasing
                h (classify l sub r p) p Hh HnotUp).
  lra.
Qed.

(* r 先頭についての双対。 *)

Lemma operated_endpoint_below_initial_stays_below_from_spec :
  forall l sub r h p,
    @ClassificationSpec l sub r (classify l sub r) ->
    0 <= h ->
    r <> [] ->
    ~ initial_lid r ->
    endpoint_of (l ++ sub ++ r) p ->
    snd p < ry0 (rect_of [hd_segment r]) ->
    snd (operate_point l sub r h p) < ry0 (rect_of [hd_segment r]).
Proof.
  intros l sub r h p Hspec Hh Hr HnotLid Hp Hbelow.
  unfold operate_point.
  pose proof (classified_below_initial_not_up
                l sub r Hspec Hr HnotLid p Hp Hbelow) as HnotUp.
  pose proof (shift_not_up_nonincreasing
                h (classify l sub r p) p Hh HnotUp).
  lra.
Qed.

(* 十分大きい移動では、各セグメントの二端点の y 座標は一致しない。 *)
Lemma operation_height_safe_from_spec :
  forall l sub r h s,
    @ClassificationSpec l sub r (classify l sub r) ->
    h_large h sub ->
    In s (l ++ sub ++ r) ->
    snd (operate_point l sub r h (init s)) <>
    snd (operate_point l sub r h (term s)).
Proof.
  intros l sub r h s Hspec Hh Hs.
  pose proof (classified_segment_endpoints_monotone
                l sub r
                Hspec
                s Hs) as [HinitTerm HtermInit].
  destruct (total_order_T (snd (init s)) (snd (term s)))
    as [[Hlt | Heq] | Hgt].
  - pose proof (shift_preserves_strict_vertical_order
                  h (init s) (term s)
                  (classify l sub r (init s))
                  (classify l sub r (term s))
                  (proj1 Hh) Hlt (HinitTerm Hlt)) as Hshift.
    unfold operate_point. lra.
  - exfalso. apply (neq_init_term_y s). exact Heq.
  - pose proof (shift_preserves_strict_vertical_order
                  h (term s) (init s)
                  (classify l sub r (term s))
                  (classify l sub r (init s))
                  (proj1 Hh) Hgt (HtermInit Hgt)) as Hshift.
    unfold operate_point. lra.
Qed.

(* 分類仕様は各セグメントの y 方向を保存する。x 方向は操作で不変。 *)
Lemma operated_segment_axis_orders_from_spec :
  forall l sub r h seg,
    @ClassificationSpec l sub r (classify l sub r) ->
    0 < h ->
    In seg (l ++ sub ++ r) ->
    (fst (init seg) < fst (term seg) <->
       fst (operate_point l sub r h (init seg)) <
       fst (operate_point l sub r h (term seg)))
    /\
    (snd (init seg) < snd (term seg) <->
       snd (operate_point l sub r h (init seg)) <
       snd (operate_point l sub r h (term seg))).
Proof.
  intros l sub r h seg Hspec Hh Hin.
  split.
  - now rewrite !operate_point_fst.
  - pose proof (classified_segment_endpoints_monotone
                  l sub r Hspec seg Hin) as [Hup Hdown].
    split.
    + intros Hy. unfold operate_point.
      eapply shift_preserves_strict_vertical_order; eauto.
    + intros Hshift.
      destruct (total_order_T (snd (init seg)) (snd (term seg)))
        as [[Hy | Heq] | Hy].
      * exact Hy.
      * exfalso. apply (neq_init_term_y seg). exact Heq.
      * exfalso. unfold operate_point in Hshift.
        pose proof (shift_preserves_strict_vertical_order
                      h (term seg) (init seg)
                      (classify l sub r (term seg))
                      (classify l sub r (init seg))
                      Hh Hy (Hdown Hy)) as Hreverse.
        lra.
Qed.

(* 一つのセグメントについて、分類された両端点を元の向きで再接続できる。 *)
Lemma operate_endpoints_reconnectable_from_spec :
  forall l sub r h,
    @ClassificationSpec l sub r (classify l sub r) ->
    h_large h sub ->
    all_reconnectable l sub r h (l ++ sub ++ r).
Proof.
  intros l sub r h Hspec Hh s Hs.
  unfold reconnectable_after, reconnectable. split.
  - rewrite !operate_point_fst. apply neq_init_term_x.
  - eapply operation_height_safe_from_spec; eauto.
Qed.

Definition same_segment_box (s t : Segment) : Prop :=
  init s = init t /\ term s = term t.

Lemma same_segment_box_rect : forall s t,
  same_segment_box s t -> rect_of [s] = rect_of [t].
Proof.
  intros s t [Hinit Hterm].
  change
    (mkRect
       (Rmin (fst (init s)) (fst (term s)))
       (Rmin (snd (init s)) (snd (term s)))
       (Rmax (fst (init s)) (fst (term s)))
       (Rmax (snd (init s)) (snd (term s))) =
     mkRect
       (Rmin (fst (init t)) (fst (term t)))
       (Rmin (snd (init t)) (snd (term t)))
       (Rmax (fst (init t)) (fst (term t)))
       (Rmax (snd (init t)) (snd (term t)))).
  now rewrite Hinit, Hterm.
Qed.

Lemma Forall2_nth_error_relation :
  forall (A B : Type) (R : A -> B -> Prop) xs ys,
    Forall2 R xs ys ->
    forall i,
      match nth_error xs i, nth_error ys i with
      | Some x, Some y => R x y
      | None, None => True
      | _, _ => False
      end.
Proof.
  intros A B R xs ys Hrel. induction Hrel.
  - intros [|i]; simpl; exact I.
  - intros [|i]; simpl; [exact H | now apply IHHrel].
Qed.

(* Spec が各端点の上下方向を保つとき、再接続列は元の primitive 列を保つ。 *)
Lemma reconnects_list_preserves_embed :
  forall l sub r h old new ds,
    @ClassificationSpec l sub r (classify l sub r) ->
    0 < h ->
    (forall s, In s old -> In s (l ++ sub ++ r)) ->
    reconnects_list_after l sub r h old new ->
    embed_listDir ds old ->
    embed_listDir ds new.
Proof.
  intros l sub r h old new ds Hspec Hh Hsubset Hrel Hembed.
  eapply embed_scurve_transfer_same_primitive; [exact Hembed | | |].
  - symmetry. now apply Forall2_length in Hrel.
  - intros i s s' Hold Hnew.
    pose proof (Forall2_nth_error_relation
                  Segment Segment (reconnects_after l sub r h)
                  old new Hrel i) as Hi.
    rewrite Hold, Hnew in Hi.
    destruct Hi as [Hinit [Hterm Horn]].
    assert (Hin : In s (l ++ sub ++ r)).
    { apply Hsubset. now apply nth_error_In in Hold. }
    destruct (operated_segment_axis_orders_from_spec
                l sub r h s Hspec Hh Hin) as [Hx Hy].
    change (init s' = ClassifyProof.operate_point l sub r h (init s)) in Hinit.
    change (term s' = ClassifyProof.operate_point l sub r h (term s)) in Hterm.
    rewrite <- Hinit, <- Hterm in Hx, Hy.
    exact (same_primitive_of_axis_orders s s' Hx Hy Horn).
  - intros i s1 s2 Hnew1 Hnew2.
    pose proof (Forall2_length Hrel) as Hlen.
    assert (Hi : (i < length old)%nat).
    { rewrite Hlen. now apply nth_error_lt in Hnew1. }
    assert (HSi : (S i < length old)%nat).
    { rewrite Hlen. now apply nth_error_lt in Hnew2. }
    destruct (nth_error old i) as [old1 |] eqn:Hold1.
    2: exfalso; apply (proj2 (nth_error_Some old i) Hi); exact Hold1.
    destruct (nth_error old (S i)) as [old2 |] eqn:Hold2.
    2: exfalso; apply (proj2 (nth_error_Some old (S i)) HSi); exact Hold2.
    pose proof (Forall2_nth_error_relation
                  Segment Segment (reconnects_after l sub r h)
                  old new Hrel i) as Hspec1.
    pose proof (Forall2_nth_error_relation
                  Segment Segment (reconnects_after l sub r h)
                  old new Hrel (S i)) as Hspec2.
    rewrite Hold1, Hnew1 in Hspec1.
    rewrite Hold2, Hnew2 in Hspec2.
    unfold reconnects_after in Hspec1, Hspec2.
    rewrite (proj1 (proj2 Hspec1)), (proj1 Hspec2).
    f_equal. exact (embed_listDir_connected ds old Hembed i old1 old2 Hold1 Hold2).
Qed.

(* split の同じ位置にある新旧セグメントは向きと operate 後の端点を共有する。 *)
Lemma ordinary_reconnect_split_nth_spec_basic :
  forall l sub r h i s s',
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (ordinary_reconnect_split l sub r h) i = Some s' ->
    orn_seg s' = orn_seg s
    /\ init s' = operate_point l sub r h (init s)
    /\ term s' = operate_point l sub r h (term s).
Proof.
  intros l sub r h i s s' Hrec Hold Hnew.
  destruct (Nat.lt_ge_cases i (length l)) as [Hil | Hil].
  - assert (Holdl : nth_error l i = Some s).
    { rewrite <- (nth_error_app1 l (sub ++ r) Hil). exact Hold. }
    assert (Hlenl : length (reconnect_segs l sub r h l) = length l).
    { apply reconnect_segs_length. }
    assert (Hnewl :
        nth_error (reconnect_segs l sub r h l) i = Some s').
    { rewrite <- Hnew. unfold ordinary_reconnect_split.
      symmetry. apply nth_error_app1. rewrite Hlenl. exact Hil. }
    rewrite (reconnect_segs_nth_error l sub r h l i s Holdl) in Hnewl.
    injection Hnewl as Heq. subst s'.
    assert (Hs : In s (l ++ sub ++ r)).
    { rewrite !in_app_iff. left. now apply nth_error_In in Holdl. }
    split.
    + apply reconnect_one_orn. exact (Hrec s Hs).
    + split.
      * apply reconnect_one_init. exact (Hrec s Hs).
      * apply reconnect_one_term. exact (Hrec s Hs).
  - set (j := (i - length l)%nat).
    assert (Holdtail : nth_error (sub ++ r) j = Some s).
    { unfold j. rewrite <- Hold. symmetry. apply nth_error_app2. lia. }
    assert (Hlenl : length (reconnect_segs l sub r h l) = length l).
    { apply reconnect_segs_length. }
    assert (Hnewtail :
        nth_error (sub ++ reconnect_segs l sub r h r) j = Some s').
    { pose proof Hnew as Hnew'. unfold ordinary_reconnect_split in Hnew'.
      rewrite nth_error_app2 in Hnew' by (rewrite Hlenl; lia).
      rewrite Hlenl in Hnew'. exact Hnew'. }
    destruct (Nat.lt_ge_cases j (length sub)) as [Hjs | Hjs].
    + assert (Holds : nth_error sub j = Some s).
      { rewrite <- Holdtail. symmetry. apply nth_error_app1. exact Hjs. }
      assert (Hnews : nth_error sub j = Some s').
      { rewrite <- Hnewtail. symmetry. apply nth_error_app1. exact Hjs. }
      rewrite Holds in Hnews. injection Hnews as Heq. subst s'.
      assert (Hins : In s sub) by now apply nth_error_In in Holds.
      repeat split; try reflexivity.
      * symmetry. apply operate_sub_endpoint; try assumption.
        exists s. split; [exact Hins | now left].
      * symmetry. apply operate_sub_endpoint; try assumption.
        exists s. split; [exact Hins | now right].
    + set (k := (j - length sub)%nat).
      assert (Holdr : nth_error r k = Some s).
      { unfold k. rewrite <- Holdtail. symmetry. apply nth_error_app2. lia. }
      assert (Hnewr :
          nth_error (reconnect_segs l sub r h r) k = Some s').
      { unfold k. rewrite <- Hnewtail. symmetry. apply nth_error_app2. lia. }
      rewrite (reconnect_segs_nth_error l sub r h r k s Holdr) in Hnewr.
      injection Hnewr as Heq. subst s'.
      assert (Hs : In s (l ++ sub ++ r)).
      { rewrite !in_app_iff. right. right. now apply nth_error_In in Holdr. }
      split.
      * apply reconnect_one_orn. exact (Hrec s Hs).
      * split.
        -- apply reconnect_one_init. exact (Hrec s Hs).
        -- apply reconnect_one_term. exact (Hrec s Hs).
Qed.

(* 従来の呼び出し形は保持し、端点仕様の実際の依存は上の基本補題に集約。 *)

Lemma ordinary_reconnect_split_connected_basic :
  forall l sub r h ds,
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    connected (ordinary_reconnect_split l sub r h).
Proof.
  intros l sub r h ds Hrec Hembed i s1 s2 Hnew1 Hnew2.
  assert (Hlen :
      length (ordinary_reconnect_split l sub r h) = length (l ++ sub ++ r)).
  { unfold ordinary_reconnect_split. repeat rewrite length_app.
    rewrite !reconnect_segs_length. reflexivity. }
  assert (Hi : (i < length (l ++ sub ++ r))%nat).
  { rewrite <- Hlen. now apply nth_error_lt in Hnew1. }
  assert (HSi : (S i < length (l ++ sub ++ r))%nat).
  { rewrite <- Hlen. now apply nth_error_lt in Hnew2. }
  destruct (nth_error (l ++ sub ++ r) i) as [old1 |] eqn:Hold1.
  2: exfalso; apply (proj2 (nth_error_Some _ _) Hi); exact Hold1.
  destruct (nth_error (l ++ sub ++ r) (S i)) as [old2 |] eqn:Hold2.
  2: exfalso; apply (proj2 (nth_error_Some _ _) HSi); exact Hold2.
  pose proof (ordinary_reconnect_split_nth_spec_basic
                l sub r h i old1 s1 Hrec Hold1 Hnew1)
    as [_ [_ Hterm]].
  pose proof (ordinary_reconnect_split_nth_spec_basic
                l sub r h (S i) old2 s2 Hrec Hold2 Hnew2)
    as [_ [Hinit _]].
  rewrite Hterm, Hinit.
  f_equal. exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed
                    i old1 old2 Hold1 Hold2).
Qed.

(* prepared 条件では、分類仕様を介して x 単調性なしに通常再接続できる。 *)
Lemma prepared_ordinary_reconnect_preserves_embed :
  forall ds l sub r h,
    PreparedGeometry l sub r ->
    @ClassificationSpec l sub r (classify l sub r) ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    embed_listDir ds (ordinary_reconnect_split l sub r h).
Proof.
  intros ds l sub r h Hgeometry Hspec Hh Hsparse Hembed Hext.
  assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
  { exact (operate_endpoints_reconnectable_from_spec l sub r h Hspec Hh). }
  eapply embed_scurve_transfer_same_primitive; [exact Hembed | | |].
  - unfold ordinary_reconnect_split. repeat rewrite length_app.
    rewrite !reconnect_segs_length. reflexivity.
  - intros i old new Hold Hnew.
    pose proof (ordinary_reconnect_split_nth_spec_basic
                  l sub r h i old new Hrec Hold Hnew)
      as [Horn [Hinit Hterm]].
    assert (Hin : In old (l ++ sub ++ r)).
    { now apply nth_error_In in Hold. }
    destruct (operated_segment_axis_orders_from_spec
                l sub r h old Hspec (proj1 Hh) Hin) as [Hx Hy].
    rewrite <- Hinit, <- Hterm in Hx, Hy.
    exact (same_primitive_of_axis_orders old new Hx Hy Horn).
  - exact (ordinary_reconnect_split_connected_basic
             l sub r h ds Hrec Hembed).
Qed.

Lemma ordinary_reconnect_split_length : forall l sub r h,
  length (ordinary_reconnect_split l sub r h) = length (l ++ sub ++ r).
Proof.
  intros. unfold ordinary_reconnect_split. repeat rewrite length_app.
  rewrite !reconnect_segs_length. reflexivity.
Qed.

Lemma strict_head_extension_same : forall s t p,
  init s = init t ->
  (forall q, onHead s q <-> onHead t q) ->
  (exists u, u < 0 /\ point s u = p) <->
  (exists u, u < 0 /\ point t u = p).
Proof.
  intros s t p Hinit Hext. split; intros [u [Hu Hp]].
  - assert (Hon : onHead s p).
    { exists u. split; [lra | exact Hp]. }
    destruct (proj1 (Hext p) Hon) as [v [Hv Hvp]].
    exists v. split; [|exact Hvp].
    destruct (Req_dec v 0) as [-> | Hneq]; [|lra].
    exfalso. apply (Rlt_irrefl 0).
    assert (Hu0 : u = 0).
    { apply (point_injective s).
      rewrite Hp, <- Hvp. change (init t = init s). now symmetry. }
    now rewrite Hu0 in Hu.
  - assert (Hon : onHead t p).
    { exists u. split; [lra | exact Hp]. }
    destruct (proj2 (Hext p) Hon) as [v [Hv Hvp]].
    exists v. split; [|exact Hvp].
    destruct (Req_dec v 0) as [-> | Hneq]; [|lra].
    exfalso. apply (Rlt_irrefl 0).
    assert (Hu0 : u = 0).
    { apply (point_injective t).
      rewrite Hp, <- Hvp. change (init s = init t). exact Hinit. }
    now rewrite Hu0 in Hu.
Qed.

Lemma strict_last_extension_same : forall s t p,
  term s = term t ->
  (forall q, onLast s q <-> onLast t q) ->
  (exists u, 1 < u /\ point s u = p) <->
  (exists u, 1 < u /\ point t u = p).
Proof.
  intros s t p Hterm Hext. split; intros [u [Hu Hp]].
  - assert (Hon : onLast s p).
    { exists u. split; [lra | exact Hp]. }
    destruct (proj1 (Hext p) Hon) as [v [Hv Hvp]].
    exists v. split; [|exact Hvp].
    destruct (Req_dec v 1) as [-> | Hneq]; [|lra].
    exfalso. apply (Rlt_irrefl 1).
    assert (Hu1 : u = 1).
    { apply (point_injective s).
      rewrite Hp, <- Hvp. change (term t = term s). now symmetry. }
    now rewrite Hu1 in Hu.
  - assert (Hon : onLast t p).
    { exists u. split; [lra | exact Hp]. }
    destruct (proj2 (Hext p) Hon) as [v [Hv Hvp]].
    exists v. split; [|exact Hvp].
    destruct (Req_dec v 1) as [-> | Hneq]; [|lra].
    exfalso. apply (Rlt_irrefl 1).
    assert (Hu1 : u = 1).
    { apply (point_injective t).
      rewrite Hp, <- Hvp. change (term s = term t). exact Hterm. }
    now rewrite Hu1 in Hu.
Qed.
