Require Export Sparse.Reconnect.
Require Export Sparse.Classify.
Require Import Stdlib.Logic.ClassicalDescription.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.

Module PreparedReconnect.

(* 再接続の端点・傾きの性質と、局所的な非交差の幾何。 *)

(* x 方向が反転する隣接セグメントの向きを [dc] から取り出す。 *)
Lemma west_to_east_dc_shapes :
  forall seg1 seg2 ps1 ps2,
    embed ps1 seg1 ->
    embed ps2 seg2 ->
    dc ps1 ps2 ->
    fst (term seg1) < fst (init seg1) ->
    fst (init seg2) < fst (term seg2) ->
    (embed (n, w, cc) seg1 /\ embed (n, e, cx) seg2)
    \/ (embed (s, w, cx) seg1 /\ embed (s, e, cc) seg2).
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
  - left. now split.
  - exfalso. pose proof (e_end_relation seg1 s cx Hemb1). lra.
  - right. now split.
Qed.

Lemma east_to_west_dc_shapes :
  forall seg1 seg2 ps1 ps2,
    embed ps1 seg1 ->
    embed ps2 seg2 ->
    dc ps1 ps2 ->
    fst (init seg1) < fst (term seg1) ->
    fst (term seg2) < fst (init seg2) ->
    (embed (n, e, cc) seg1 /\ embed (n, w, cx) seg2)
    \/ (embed (s, e, cx) seg1 /\ embed (s, w, cc) seg2).
Proof.
  intros seg1 seg2 ps1 ps2 Hemb1 Hemb2 Hdc Heast Hwest.
  destruct Hdc; destruct h.
  - exfalso. pose proof (e_end_relation seg2 v (i_c c) Hemb2). lra.
  - exfalso. pose proof (w_end_relation seg1 v c Hemb1). lra.
  - exfalso. pose proof (e_end_relation seg2 s cx Hemb2). lra.
  - exfalso. pose proof (w_end_relation seg1 n cx Hemb1). lra.
  - exfalso. pose proof (e_end_relation seg2 n cc Hemb2). lra.
  - exfalso. pose proof (w_end_relation seg1 s cc Hemb1). lra.
  - left. now split.
  - exfalso. pose proof (w_end_relation seg1 n cc Hemb1). lra.
  - right. now split.
  - exfalso. pose proof (w_end_relation seg1 s cx Hemb1). lra.
Qed.

(* x 方向を折り返して接続するとき、二セグメントの y 方向は一致する。 *)
Lemma west_to_east_dc_vertical_order :
  forall seg1 seg2 ps1 ps2,
    embed ps1 seg1 -> embed ps2 seg2 -> dc ps1 ps2 ->
    fst (term seg1) < fst (init seg1) ->
    fst (init seg2) < fst (term seg2) ->
    (snd (init seg2) < snd (term seg2) ->
       snd (init seg1) < snd (term seg1)) /\
    (snd (term seg2) < snd (init seg2) ->
       snd (term seg1) < snd (init seg1)).
Proof.
  intros seg1 seg2 ps1 ps2 Hemb1 Hemb2 Hdc Hwest Heast.
  destruct (west_to_east_dc_shapes
              seg1 seg2 ps1 ps2 Hemb1 Hemb2 Hdc Hwest Heast)
    as [[Hn1 Hn2] | [Hs1 Hs2]].
  - split; intros; [exact (n_end_relation seg1 w cc Hn1) |].
    exfalso. pose proof (n_end_relation seg2 e cx Hn2). lra.
  - split; intros; [|exact (s_end_relation seg1 w cx Hs1)].
    exfalso. pose proof (s_end_relation seg2 e cc Hs2). lra.
Qed.

Lemma east_to_west_dc_vertical_order :
  forall seg1 seg2 ps1 ps2,
    embed ps1 seg1 -> embed ps2 seg2 -> dc ps1 ps2 ->
    fst (init seg1) < fst (term seg1) ->
    fst (term seg2) < fst (init seg2) ->
    (snd (init seg1) < snd (term seg1) ->
       snd (init seg2) < snd (term seg2)) /\
    (snd (term seg1) < snd (init seg1) ->
       snd (term seg2) < snd (init seg2)).
Proof.
  intros seg1 seg2 ps1 ps2 Hemb1 Hemb2 Hdc Heast Hwest.
  destruct (east_to_west_dc_shapes
              seg1 seg2 ps1 ps2 Hemb1 Hemb2 Hdc Heast Hwest)
    as [[Hn1 Hn2] | [Hs1 Hs2]].
  - split; intros; [exact (n_end_relation seg2 w cx Hn2) |].
    exfalso. pose proof (n_end_relation seg1 e cc Hn1). lra.
  - split; intros; [|exact (s_end_relation seg2 w cc Hs2)].
    exfalso. pose proof (s_end_relation seg1 e cx Hs1). lra.
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
    ClassificationSpec l sub r ->
    (l <> [] -> reconnect_init_slope_after l sub r h (hd_segment l)) ->
    onHead_extend (reconnect_whole l sub r h) p ->
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
    ClassificationSpec l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    (r <> [] -> reconnect_term_slope_after l sub r h (last_segment r)) ->
    onLast_extend (reconnect_whole l sub r h) p ->
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
      last_segment (reconnect_whole l sub [] h) = last_segment sub).
    { unfold reconnect_whole, reconnect_segs. simpl. rewrite app_nil_r.
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
      last_segment (reconnect_whole l sub (a :: r') h) =
      reconnect_one l sub (a :: r') h (last_segment (a :: r'))).
    { unfold reconnect_whole, reconnect_segs.
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
    ClassificationSpec l sub r ->
    0 <= h ->
    onHead_extend_strict (reconnect_whole l sub r h) p ->
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
    ClassificationSpec l sub r ->
    0 <= h ->
    onLast_extend_strict (reconnect_whole l sub r h) p ->
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
      last_segment (reconnect_whole l sub [] h) = last_segment sub).
    { unfold reconnect_whole, reconnect_segs. simpl. rewrite app_nil_r.
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
      last_segment (reconnect_whole l sub (a :: r') h) =
      reconnect_one l sub (a :: r') h (last_segment (a :: r'))).
    { unfold reconnect_whole, reconnect_segs.
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

(* 十分大きい移動では、各セグメントの二端点の y 座標は一致しない。 *)
Lemma operation_height_safe_from_spec :
  forall l sub r h s,
    ClassificationSpec l sub r ->
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
    ClassificationSpec l sub r ->
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
    ClassificationSpec l sub r ->
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
    ClassificationSpec l sub r ->
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
Lemma reconnect_whole_nth_spec :
  forall l sub r h i s s',
    ClassificationSpec l sub r ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (reconnect_whole l sub r h) i = Some s' ->
    orn_seg s' = orn_seg s
    /\ init s' = operate_point l sub r h (init s)
    /\ term s' = operate_point l sub r h (term s).
Proof.
  intros l sub r h i s s' Hspec Hrec Hold Hnew.
  destruct (Nat.lt_ge_cases i (length l)) as [Hil | Hil].
  - assert (Holdl : nth_error l i = Some s).
    { rewrite <- (nth_error_app1 l (sub ++ r) Hil). exact Hold. }
    assert (Hlenl : length (reconnect_segs l sub r h l) = length l).
    { apply reconnect_segs_length. }
    assert (Hnewl :
        nth_error (reconnect_segs l sub r h l) i = Some s').
    { rewrite <- Hnew. unfold reconnect_whole.
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
    { pose proof Hnew as Hnew'. unfold reconnect_whole in Hnew'.
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
      * symmetry. apply operate_point_RegFix.
        apply (classified_sub_fixed l sub r Hspec).
        exists s. split; [exact Hins | apply onInit].
      * symmetry. apply operate_point_RegFix.
        apply (classified_sub_fixed l sub r Hspec).
        exists s. split; [exact Hins | apply onTerm].
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

Lemma reconnect_whole_connected :
  forall l sub r h ds,
    ClassificationSpec l sub r ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    connected (reconnect_whole l sub r h).
Proof.
  intros l sub r h ds Hspec Hrec Hembed i s1 s2 Hnew1 Hnew2.
  assert (Hlen :
      length (reconnect_whole l sub r h) = length (l ++ sub ++ r)).
  { unfold reconnect_whole. repeat rewrite length_app.
    rewrite !reconnect_segs_length. reflexivity. }
  assert (Hi : (i < length (l ++ sub ++ r))%nat).
  { rewrite <- Hlen. now apply nth_error_lt in Hnew1. }
  assert (HSi : (S i < length (l ++ sub ++ r))%nat).
  { rewrite <- Hlen. now apply nth_error_lt in Hnew2. }
  destruct (nth_error (l ++ sub ++ r) i) as [old1 |] eqn:Hold1.
  2: exfalso; apply (proj2 (nth_error_Some _ _) Hi); exact Hold1.
  destruct (nth_error (l ++ sub ++ r) (S i)) as [old2 |] eqn:Hold2.
  2: exfalso; apply (proj2 (nth_error_Some _ _) HSi); exact Hold2.
  pose proof (reconnect_whole_nth_spec
                l sub r h i old1 s1 Hspec Hrec Hold1 Hnew1)
    as [_ [_ Hterm]].
  pose proof (reconnect_whole_nth_spec
                l sub r h (S i) old2 s2 Hspec Hrec Hold2 Hnew2)
    as [_ [Hinit _]].
  rewrite Hterm, Hinit.
  f_equal. exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed
                    i old1 old2 Hold1 Hold2).
Qed.

(* prepared 条件では、分類仕様を介して x 単調性なしに通常再接続できる。 *)
Lemma prepared_reconnect_whole_preserves_embed :
  forall ds l sub r h,
    PreparedGeometry l sub r ->
    ClassificationSpec l sub r ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    embed_listDir ds (reconnect_whole l sub r h).
Proof.
  intros ds l sub r h Hgeometry Hspec Hh Hsparse Hembed Hext.
  assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
  { exact (operate_endpoints_reconnectable_from_spec l sub r h Hspec Hh). }
  eapply embed_scurve_transfer_same_primitive; [exact Hembed | | |].
  - unfold reconnect_whole. repeat rewrite length_app.
    rewrite !reconnect_segs_length. reflexivity.
  - intros i old new Hold Hnew.
    pose proof (reconnect_whole_nth_spec
                  l sub r h i old new Hspec Hrec Hold Hnew)
      as [Horn [Hinit Hterm]].
    assert (Hin : In old (l ++ sub ++ r)).
    { now apply nth_error_In in Hold. }
    destruct (operated_segment_axis_orders_from_spec
                l sub r h old Hspec (proj1 Hh) Hin) as [Hx Hy].
    rewrite <- Hinit, <- Hterm in Hx, Hy.
    exact (same_primitive_of_axis_orders old new Hx Hy Horn).
  - exact (reconnect_whole_connected
             l sub r h ds Hspec Hrec Hembed).
Qed.

Lemma reconnect_whole_length : forall l sub r h,
  length (reconnect_whole l sub r h) = length (l ++ sub ++ r).
Proof.
  intros. unfold reconnect_whole. repeat rewrite length_app.
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

(* 再接続後の端点長方形・延長線・sub 周辺の局所分離。 *)
Definition endpoint_rectangles_axis_separated (s t : Segment) : Prop :=
     rx1 (rect_of [t]) < rx0 (rect_of [s])
  \/ rx1 (rect_of [s]) < rx0 (rect_of [t])
  \/ ry1 (rect_of [t]) < ry0 (rect_of [s])
  \/ ry1 (rect_of [s]) < ry0 (rect_of [t]).

Lemma singleton_rect_positive : forall s,
  rx0 (rect_of [s]) < rx1 (rect_of [s])
  /\ ry0 (rect_of [s]) < ry1 (rect_of [s]).
Proof.
  intros s. unfold rect_of; simpl. split.
  - destruct (total_order_T (fst (init s)) (fst (term s)))
      as [[Hlt | Heq] | Hgt].
    + rewrite Rmin_left by now apply Rlt_le.
      rewrite Rmax_right by now apply Rlt_le. exact Hlt.
    + exfalso. apply (neq_init_term_x s). exact Heq.
    + rewrite Rmin_right by now apply Rlt_le.
      rewrite Rmax_left by now apply Rlt_le. exact Hgt.
  - destruct (total_order_T (snd (init s)) (snd (term s)))
      as [[Hlt | Heq] | Hgt].
    + rewrite Rmin_left by now apply Rlt_le.
      rewrite Rmax_right by now apply Rlt_le. exact Hlt.
    + exfalso. apply (neq_init_term_y s). exact Heq.
    + rewrite Rmin_right by now apply Rlt_le.
      rewrite Rmax_left by now apply Rlt_le. exact Hgt.
Qed.

(* 一方の端点長方形が他方を避ければ、二長方形は軸方向に分離する。 *)
Lemma rectangles_avoid_implies_axis_separated : forall s t,
  (forall p,
    in_segment_rect_or_endpoints t p ->
    ~ in_rect_or_endpoints_at [s] p) ->
  endpoint_rectangles_axis_separated s t.
Proof.
  intros s t Havoid. unfold endpoint_rectangles_axis_separated.
  destruct (classic (rx1 (rect_of [t]) < rx0 (rect_of [s]))) as [H | H]; [now left|].
  destruct (classic (rx1 (rect_of [s]) < rx0 (rect_of [t]))) as [H' | H']; [now right; left|].
  destruct (classic (ry1 (rect_of [t]) < ry0 (rect_of [s]))) as [Hy | Hy]; [now right; right; left|].
  destruct (classic (ry1 (rect_of [s]) < ry0 (rect_of [t]))) as [Hy' | Hy']; [now right; right; right|].
  destruct (singleton_rect_positive s) as [Hsx Hsy].
  destruct (singleton_rect_positive t) as [Htx Hty].
  set (x := Rmax (rx0 (rect_of [s])) (rx0 (rect_of [t]))).
  set (y := Rmax (ry0 (rect_of [s])) (ry0 (rect_of [t]))).
  assert (Hxs : rx0 (rect_of [s]) <= x <= rx1 (rect_of [s])).
  { split; [unfold x; apply Rmax_l |].
    unfold x. apply Rmax_lub; [lra | now apply Rnot_lt_le]. }
  assert (Hxt : rx0 (rect_of [t]) <= x <= rx1 (rect_of [t])).
  { split; [unfold x; apply Rmax_r |].
    unfold x. apply Rmax_lub; [now apply Rnot_lt_le | lra]. }
  assert (Hys : ry0 (rect_of [s]) <= y <= ry1 (rect_of [s])).
  { split; [unfold y; apply Rmax_l |].
    unfold y. apply Rmax_lub; [lra | now apply Rnot_lt_le]. }
  assert (Hyt : ry0 (rect_of [t]) <= y <= ry1 (rect_of [t])).
  { split; [unfold y; apply Rmax_r |].
    unfold y. apply Rmax_lub; [now apply Rnot_lt_le | lra]. }
  exfalso.
  apply (Havoid (x, y)).
  - unfold in_segment_rect_or_endpoints, in_closed_rect; simpl.
    exact (conj Hxt Hyt).
  - unfold in_rect_or_endpoints_at, in_closed_rect; simpl.
    exact (conj Hxs Hys).
Qed.

Lemma in_segment_rect_or_endpoints_closed_bounds : forall s p,
  in_segment_rect_or_endpoints s p ->
  rx0 (rect_of [s]) <= fst p <= rx1 (rect_of [s])
  /\ ry0 (rect_of [s]) <= snd p <= ry1 (rect_of [s]).
Proof.
  intros s p Hp. exact Hp.
Qed.

(* 軸方向に厳密に分離した二閉長方形は互いに交わらない。 *)
Lemma axis_separated_boxes_avoid : forall s t,
  endpoint_rectangles_axis_separated s t ->
  forall p,
    in_segment_rect_or_endpoints t p ->
    ~ in_rect_or_endpoints_at [s] p.
Proof.
  intros s t Haxis p Hp Hs.
  unfold in_segment_rect_or_endpoints, in_rect_or_endpoints_at,
    in_closed_rect in Hp, Hs.
  unfold endpoint_rectangles_axis_separated in Haxis.
  destruct Haxis as [Haxis | [Haxis | [Haxis | Haxis]]]; lra.
Qed.

(* 端点間の分類順序により、旧長方形の軸方向の分離は移動後も保たれる。 *)
Lemma operated_endpoint_rectangles_axis_separated_from_order :
  forall l sub r h i j s t s' t',
    0 < h ->
    (forall pt ps,
      segment_x_ranges_overlap t s ->
      endpoint_of_seg t pt -> endpoint_of_seg s ps ->
      snd pt < snd ps ->
      snd (operate_point l sub r h pt) <
      snd (operate_point l sub r h ps)) ->
    (forall ps pt,
      segment_x_ranges_overlap s t ->
      endpoint_of_seg s ps -> endpoint_of_seg t pt ->
      snd ps < snd pt ->
      snd (operate_point l sub r h ps) <
      snd (operate_point l sub r h pt)) ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (l ++ sub ++ r) j = Some t ->
    (S i < j \/ S j < i)%nat ->
    init s' = operate_point l sub r h (init s) ->
    term s' = operate_point l sub r h (term s) ->
    init t' = operate_point l sub r h (init t) ->
    term t' = operate_point l sub r h (term t) ->
    endpoint_rectangles_axis_separated s t ->
    endpoint_rectangles_axis_separated s' t'.
Proof.
  intros l sub r h i j s t s' t' Hh HorderTS HorderST
    Hs Ht Hfar Hsinit Hsterm Htinit Htterm Haxis.
  unfold endpoint_rectangles_axis_separated in Haxis |- *.
  assert (Hhorizontal_or_overlap :
      rx1 (rect_of [t]) < rx0 (rect_of [s])
      \/ rx1 (rect_of [s]) < rx0 (rect_of [t])
      \/ segment_x_ranges_overlap s t).
  { destruct (classic (rx1 (rect_of [t]) < rx0 (rect_of [s])))
      as [Hleft | Hleft]; [now left|].
    destruct (classic (rx1 (rect_of [s]) < rx0 (rect_of [t])))
      as [Hright | Hright]; [now right; left|].
    right; right. unfold segment_x_ranges_overlap. lra. }
  destruct Hhorizontal_or_overlap as [Hleft | [Hright | Hoverlap]].
  - left.
    change (Rmax (fst (init t')) (fst (term t')) <
            Rmin (fst (init s')) (fst (term s'))).
    change (Rmax (fst (init t)) (fst (term t)) <
            Rmin (fst (init s)) (fst (term s))) in Hleft.
    rewrite Hsinit, Hsterm, Htinit, Htterm.
    rewrite !operate_point_fst. exact Hleft.
  - right; left.
    change (Rmax (fst (init s')) (fst (term s')) <
            Rmin (fst (init t')) (fst (term t'))).
    change (Rmax (fst (init s)) (fst (term s)) <
            Rmin (fst (init t)) (fst (term t))) in Hright.
    rewrite Hsinit, Hsterm, Htinit, Htterm.
    rewrite !operate_point_fst. exact Hright.
  - destruct Haxis as [Hleft' | [Hright' | [Hbelow | Habove]]].
    + unfold segment_x_ranges_overlap in Hoverlap. lra.
    + unfold segment_x_ranges_overlap in Hoverlap. lra.
    + right; right; left.
    change (Rmax (snd (init t')) (snd (term t')) <
            Rmin (snd (init s')) (snd (term s'))).
    rewrite Hsinit, Hsterm, Htinit, Htterm.
    change (Rmax (snd (init t)) (snd (term t)) <
            Rmin (snd (init s)) (snd (term s))) in Hbelow.
    assert (Hold : forall pt ps,
      endpoint_of_seg t pt -> endpoint_of_seg s ps -> snd pt < snd ps).
    { intros pt ps Hpt Hps. destruct Hpt as [-> | ->]; destruct Hps as [-> | ->];
        pose proof (Rmax_l (snd (init t)) (snd (term t)));
        pose proof (Rmax_r (snd (init t)) (snd (term t)));
        pose proof (Rmin_l (snd (init s)) (snd (term s)));
        pose proof (Rmin_r (snd (init s)) (snd (term s))); lra. }
    assert (Hfar' : (S j < i \/ S i < j)%nat) by tauto.
    assert (Hoverlap' : segment_x_ranges_overlap t s).
    { unfold segment_x_ranges_overlap in *. tauto. }
    apply Rmax_lub_lt; apply Rmin_glb_lt.
    * eapply HorderTS; [exact Hoverlap' | now left | now left | apply Hold; now left].
    * eapply HorderTS; [exact Hoverlap' | now left | now right | apply Hold; [now left | now right]].
    * eapply HorderTS; [exact Hoverlap' | now right | now left | apply Hold; [now right | now left]].
    * eapply HorderTS; [exact Hoverlap' | now right | now right | apply Hold; now right].
    + right; right; right.
    change (Rmax (snd (init s')) (snd (term s')) <
            Rmin (snd (init t')) (snd (term t'))).
    rewrite Hsinit, Hsterm, Htinit, Htterm.
    change (Rmax (snd (init s)) (snd (term s)) <
            Rmin (snd (init t)) (snd (term t))) in Habove.
    assert (Hold : forall ps pt,
      endpoint_of_seg s ps -> endpoint_of_seg t pt -> snd ps < snd pt).
    { intros ps pt Hps Hpt. destruct Hps as [-> | ->]; destruct Hpt as [-> | ->];
        pose proof (Rmax_l (snd (init s)) (snd (term s)));
        pose proof (Rmax_r (snd (init s)) (snd (term s)));
        pose proof (Rmin_l (snd (init t)) (snd (term t)));
        pose proof (Rmin_r (snd (init t)) (snd (term t))); lra. }
    apply Rmax_lub_lt; apply Rmin_glb_lt.
    * eapply HorderST; [exact Hoverlap | now left | now left | apply Hold; now left].
    * eapply HorderST; [exact Hoverlap | now left | now right | apply Hold; [now left | now right]].
    * eapply HorderST; [exact Hoverlap | now right | now left | apply Hold; [now right | now left]].
    * eapply HorderST; [exact Hoverlap | now right | now right | apply Hold; now right].
Qed.

(* 蓋なしなら固定 sub 端点も同じ順序仕様の対象となる。 *)
Lemma operated_endpoint_rectangles_axis_separated_no_lid :
  forall l sub r h i j s t s' t',
    ClassificationSpec l sub r ->
    ~ terminal_lid l sub r ->
    ~ initial_lid l sub r ->
    0 < h ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (l ++ sub ++ r) j = Some t ->
    (S i < j \/ S j < i)%nat ->
    init s' = operate_point l sub r h (init s) ->
    term s' = operate_point l sub r h (term s) ->
    init t' = operate_point l sub r h (init t) ->
    term t' = operate_point l sub r h (term t) ->
    endpoint_rectangles_axis_separated s t ->
    endpoint_rectangles_axis_separated s' t'.
Proof.
  intros l sub r h i j s t s' t' Hspec HnoTerminal HnoInitial Hh
    Hs Ht Hfar Hsinit Hsterm Htinit Htterm Haxis.
  eapply operated_endpoint_rectangles_axis_separated_from_order;
    [exact Hh | | | exact Hs | exact Ht | exact Hfar |
     exact Hsinit | exact Hsterm | exact Htinit | exact Htterm | exact Haxis].
  - intros pt ps Hover Hpt Hps Hy.
    assert (Hfar' : (S j < i \/ S i < j)%nat) by tauto.
    unfold operate_point.
    eapply shift_preserves_strict_vertical_order;
      [exact Hh | exact Hy |].
    exact (classified_nonadjacent_endpoint_order_no_lid
             l sub r Hspec HnoTerminal HnoInitial
             j i t s pt ps Ht Hs Hfar' Hover Hpt Hps
             (Rlt_le _ _ Hy)).
  - intros ps pt Hover Hps Hpt Hy.
    unfold operate_point.
    eapply shift_preserves_strict_vertical_order;
      [exact Hh | exact Hy |].
    exact (classified_nonadjacent_endpoint_order_no_lid
             l sub r Hspec HnoTerminal HnoInitial
             i j s t ps pt Hs Ht Hfar Hover Hps Hpt
             (Rlt_le _ _ Hy)).
Qed.

(* 延長線点と同じ x の旧セグメント点が与える分類順序から，
   延長線点は移動後の端点長方形にも入らない。 *)
Lemma shifted_crossing_avoids_endpoint_rect :
  forall h s s' q g gi gt,
    0 < h ->
    init s' = shift h gi (init s) ->
    term s' = shift h gt (term s) ->
    ~ in_rect_or_endpoints_at [s] q ->
    (forall e,
      onSegment s e ->
      fst e = fst q ->
      (snd q < snd e ->
         region_at_or_above gi g /\ region_at_or_above gt g)
      /\
      (snd e < snd q ->
         region_at_or_above g gi /\ region_at_or_above g gt)) ->
    ~ in_rect_or_endpoints_at [s'] (shift h g q).
Proof.
  intros h s s' q g gi gt Hh Hinit Hterm Hold Hcross Hnew.
  unfold in_rect_or_endpoints_at, in_closed_rect in Hold, Hnew.
  change
    (~ ((Rmin (fst (init s)) (fst (term s)) <= fst q <=
          Rmax (fst (init s)) (fst (term s))) /\
         (Rmin (snd (init s)) (snd (term s)) <= snd q <=
          Rmax (snd (init s)) (snd (term s))))) in Hold.
  change
    ((Rmin (fst (init s')) (fst (term s')) <= fst (shift h g q) <=
       Rmax (fst (init s')) (fst (term s'))) /\
     (Rmin (snd (init s')) (snd (term s')) <= snd (shift h g q) <=
       Rmax (snd (init s')) (snd (term s')))) in Hnew.
  rewrite Hinit, Hterm, !shift_fst in Hnew.
  destruct Hnew as [Hqx Hqy].
  destruct (segment_has_point_at_x s (fst q) Hqx) as [e [He Hxe]].
  pose proof (segment_in_rect_or_endpoints s e He) as Hebounds.
  unfold in_segment_rect_or_endpoints, in_closed_rect in Hebounds.
  change
    ((Rmin (fst (init s)) (fst (term s)) <= fst e <=
       Rmax (fst (init s)) (fst (term s))) /\
     (Rmin (snd (init s)) (snd (term s)) <= snd e <=
       Rmax (snd (init s)) (snd (term s)))) in Hebounds.
  assert (Hvertical :
      snd q < Rmin (snd (init s)) (snd (term s))
      \/ Rmax (snd (init s)) (snd (term s)) < snd q).
  { destruct (Rlt_dec (snd q) (Rmin (snd (init s)) (snd (term s))))
      as [Hbelow | Hbelow]; [now left | right].
    apply Rnot_le_lt. intro Habove.
    apply Hold. split; [exact Hqx |].
    split; [apply Rnot_lt_le in Hbelow; exact Hbelow | exact Habove]. }
  destruct Hvertical as [Hbelow | Habove].
  - assert (Hqe : snd q < snd e) by lra.
    pose proof (proj1 (Hcross e He Hxe) Hqe) as [Hgi Hgt].
    assert (Hqi : snd q < snd (init s)).
    { pose proof (Rmin_l (snd (init s)) (snd (term s))). lra. }
    assert (Hqt : snd q < snd (term s)).
    { pose proof (Rmin_r (snd (init s)) (snd (term s))). lra. }
    pose proof (shift_preserves_strict_vertical_order
                  h q (init s) g gi Hh Hqi Hgi) as Hnewi.
    pose proof (shift_preserves_strict_vertical_order
                  h q (term s) g gt Hh Hqt Hgt) as Hnewt.
    assert (Hnewmin :
      snd (shift h g q) <
      Rmin (snd (shift h gi (init s))) (snd (shift h gt (term s)))).
    { now apply Rmin_glb_lt. }
    exact (Rlt_not_le _ _ Hnewmin (proj1 Hqy)).
  - assert (Heq : snd e < snd q) by lra.
    pose proof (proj2 (Hcross e He Hxe) Heq) as [Hig Htg].
    assert (Hiq : snd (init s) < snd q).
    { pose proof (Rmax_l (snd (init s)) (snd (term s))). lra. }
    assert (Htq : snd (term s) < snd q).
    { pose proof (Rmax_r (snd (init s)) (snd (term s))). lra. }
    pose proof (shift_preserves_strict_vertical_order
                  h (init s) q gi g Hh Hiq Hig) as Hnewi.
    pose proof (shift_preserves_strict_vertical_order
                  h (term s) q gt g Hh Htq Htg) as Hnewt.
    assert (Hnewmax :
      Rmax (snd (shift h gi (init s))) (snd (shift h gt (term s))) <
      snd (shift h g q)).
    { now apply Rmax_lub_lt. }
    exact (Rlt_not_le _ _ Hnewmax (proj2 Hqy)).
Qed.

Definition nonadjacent_bodies_disjoint (ls : list Segment) : Prop :=
  forall i j s t p,
    nth_error ls i = Some s ->
    nth_error ls j = Some t ->
    (S i < j \/ S j < i)%nat ->
    onSegment s p ->
    onSegment t p ->
    False.

(* 全体始点と正パラメータ本体の衝突は、先頭自身なら単射性、直後なら
   dc、それ以降なら非隣接本体非交差で直接排除できる。 *)
Lemma embedded_nonadjacent_initial_point_avoids_positive_body :
  forall ds ls,
    embed_listDir ds ls ->
    nonadjacent_bodies_disjoint ls ->
    forall i s u,
      nth_error ls i = Some s ->
      0 < u <= 1 ->
      init (hd_segment ls) <> point s u.
Proof.
  intros ds ls Hembed Hfar.
  destruct ls as [|first rest].
  { intros i s u Hnth Hu. destruct i; discriminate. }
  intros i s u Hnth Hu.
  destruct i as [|i].
  - simpl in Hnth. injection Hnth as <-.
    intro Heq.
    assert (Hu0 : u = 0).
    { apply (point_injective first).
      change (point first u = init first). now symmetry. }
    lra.
  - destruct i as [|i].
    + destruct rest as [|second rest]; [discriminate |].
      simpl in Hnth. injection Hnth as <-.
      intros Heq.
      destruct Hembed as [sc [_ Hcurve]].
      destruct (embed_scurve_adjacent_data
                  sc (first :: second :: rest) 0 first second
                  Hcurve eq_refl eq_refl)
        as [ps [pt [Hfirst [Hsecond [Hdc Hjoin]]]]].
      assert (HonFirst : onSegment first (init first)) by apply onInit.
      assert (HonSecond : onSegment second (init first)).
      { exists u. split; [lra | now symmetry]. }
      pose proof (adjacent_not_intersect_except_junction
                    ps pt first second (init first)
                    Hdc Hfirst Hsecond Hjoin HonFirst HonSecond) as HeqEnds.
      apply (neq_init_term_y first).
      now apply (f_equal snd) in HeqEnds.
    + intros Heq.
      eapply (Hfar 0%nat (S (S i)) first s (init first)).
      * reflexivity.
      * exact Hnth.
      * left. lia.
      * apply onInit.
      * exists u. split; [lra | now symmetry].
Qed.

Definition both_left_of_sub (sub : list Segment) (p q : Point) : Prop :=
  fst p < rx0 (rect_of sub) /\ fst q < rx0 (rect_of sub).

Definition both_right_of_sub (sub : list Segment) (p q : Point) : Prop :=
  rx1 (rect_of sub) < fst p /\ rx1 (rect_of sub) < fst q.

Definition both_above_of_sub (sub : list Segment) (p q : Point) : Prop :=
  ry1 (bbox_of sub) < snd p /\ ry1 (bbox_of sub) < snd q.

Definition both_below_of_sub (sub : list Segment) (p q : Point) : Prop :=
  snd p < ry0 (bbox_of sub) /\ snd q < ry0 (bbox_of sub).

Definition endpoint_box_separated_from_sub
  (sub : list Segment) (p q : Point) : Prop :=
     both_above_of_sub sub p q
  \/ both_below_of_sub sub p q
  \/ both_left_of_sub sub p q
  \/ both_right_of_sub sub p q.

Lemma segment_rect_has_positive_width :
  forall s, rx0 (rect_of [s]) < rx1 (rect_of [s]).
Proof.
  intros s.
  change (Rmin (fst (init s)) (fst (term s)) <
          Rmax (fst (init s)) (fst (term s))).
  destruct (total_order_T (fst (init s)) (fst (term s)))
    as [[Hlt | Heq] | Hgt].
  - rewrite Rmin_left by lra. rewrite Rmax_right by lra. exact Hlt.
  - exfalso. apply (neq_init_term_x s).
    unfold init_x, term_x. exact Heq.
  - rewrite Rmin_right by lra. rewrite Rmax_left by lra. exact Hgt.
Qed.

(* 二つの閉区間が互いを飛び越していなければ共通点を持つ。 *)
Lemma closed_intervals_have_common_point :
  forall a0 a1 b0 b1,
    a0 <= a1 -> b0 <= b1 -> a0 <= b1 -> b0 <= a1 ->
    exists x, a0 <= x <= a1 /\ b0 <= x <= b1.
Proof.
  intros a0 a1 b0 b1 Ha Hb Hab Hba.
  exists (Rmax a0 b0). split.
  - split; [apply Rmax_l | apply Rmax_lub; assumption].
  - split; [apply Rmax_r | apply Rmax_lub; assumption].
Qed.

(* 左右の同じ側に厳密に固まらない二端点の閉 x 区間は共通する。
   この区間の事実には sub の x 単調性を使わない。 *)
Lemma nonhorizontal_sides_have_common_x :
  forall sub s,
    ~ both_left_of_sub sub (init s) (term s) ->
    ~ both_right_of_sub sub (init s) (term s) ->
    exists x,
      rx0 (rect_of sub) <= x <= rx1 (rect_of sub)
      /\ rx0 (rect_of [s]) <= x <= rx1 (rect_of [s]).
Proof.
  intros sub s Hleft Hright.
  assert (Hsub : rx0 (rect_of sub) <= rx1 (rect_of sub)).
  { unfold rect_of; simpl; unfold Rmin, Rmax;
      repeat destruct Rle_dec; lra. }
  pose proof (segment_rect_has_positive_width s) as Hseg.
  assert (HcrossL : rx0 (rect_of sub) <= rx1 (rect_of [s])).
  { apply Rnot_lt_le. intro Hlt. apply Hleft.
    unfold both_left_of_sub, rect_of in *; simpl in *.
    split.
    - eapply Rle_lt_trans; [apply Rmax_l | exact Hlt].
    - eapply Rle_lt_trans; [apply Rmax_r | exact Hlt]. }
  assert (HcrossR : rx0 (rect_of [s]) <= rx1 (rect_of sub)).
  { apply Rnot_lt_le. intro Hlt. apply Hright.
    unfold both_right_of_sub, rect_of in *; simpl in *.
    split.
    - eapply Rlt_le_trans; [exact Hlt | apply Rmin_l].
    - eapply Rlt_le_trans; [exact Hlt | apply Rmin_r]. }
  apply closed_intervals_have_common_point; lra.
Qed.

(* 同じ x の sub 上の点より上を通る非隣接セグメントは、両端とも
   bbox の下端以上にある。 *)
Lemma above_sub_point_bounds_segment_endpoints :
  forall l sub r s p q,
    sparse_embedding (l ++ sub ++ r) ->
    In s (nonadjacent_sides l r) ->
    onSegment s p ->
    onSegmentlist sub q ->
    rx0 (rect_of [s]) <= fst q <= rx1 (rect_of [s]) ->
    snd q < snd p ->
    ry0 (bbox_of sub) <= snd (init s)
    /\ ry0 (bbox_of sub) <= snd (term s).
Proof.
  intros l sub r s p q Hsparse Hs Hp Hq Hqx Hy.
  unfold rect_of in Hqx; simpl in Hqx.
  pose proof (bbox_of_bounds sub q Hq) as [Hqlo _].
  pose proof (segment_in_rect_or_endpoints s p Hp) as Hpbox.
  assert (Hpy : Rmin (snd (init s)) (snd (term s)) <= snd p
                <= Rmax (snd (init s)) (snd (term s))).
  { unfold in_segment_rect_or_endpoints, in_closed_rect in Hpbox.
    change
      ((Rmin (fst (init s)) (fst (term s)) <= fst p <=
          Rmax (fst (init s)) (fst (term s))) /\
       (Rmin (snd (init s)) (snd (term s)) <= snd p <=
          Rmax (snd (init s)) (snd (term s)))) in Hpbox.
    exact (proj2 Hpbox). }
  assert (Havoid := sparse_nonadjacent_box_avoids_sub_points
                       l sub r s q Hsparse Hs Hq).
  split; apply Rnot_lt_le; intro Hend.
  - apply Havoid.
    unfold in_segment_rect_or_endpoints, in_closed_rect, rect_of; simpl.
    split; [lra |].
    destruct Hpy as [Hpy0 Hpy1].
    split.
    + eapply Rle_trans; [apply Rmin_l |].
      eapply Rle_trans; [apply Rlt_le; exact Hend | exact Hqlo].
    + eapply Rle_trans; [apply Rlt_le; exact Hy | exact Hpy1].
  - apply Havoid.
    unfold in_segment_rect_or_endpoints, in_closed_rect, rect_of; simpl.
    split; [lra |].
    destruct Hpy as [Hpy0 Hpy1].
    split.
    + eapply Rle_trans; [apply Rmin_r |].
      eapply Rle_trans; [apply Rlt_le; exact Hend | exact Hqlo].
    + eapply Rle_trans; [apply Rlt_le; exact Hy | exact Hpy1].
Qed.

(* 下側の場合の双対。両端とも bbox の上端以下にある。 *)
Lemma below_sub_point_bounds_segment_endpoints :
  forall l sub r s p q,
    sparse_embedding (l ++ sub ++ r) ->
    In s (nonadjacent_sides l r) ->
    onSegment s p ->
    onSegmentlist sub q ->
    rx0 (rect_of [s]) <= fst q <= rx1 (rect_of [s]) ->
    snd p < snd q ->
    snd (init s) <= ry1 (bbox_of sub)
    /\ snd (term s) <= ry1 (bbox_of sub).
Proof.
  intros l sub r s p q Hsparse Hs Hp Hq Hqx Hy.
  unfold rect_of in Hqx; simpl in Hqx.
  pose proof (bbox_of_bounds sub q Hq) as [_ Hqhi].
  pose proof (segment_in_rect_or_endpoints s p Hp) as Hpbox.
  assert (Hpy : Rmin (snd (init s)) (snd (term s)) <= snd p
                <= Rmax (snd (init s)) (snd (term s))).
  { unfold in_segment_rect_or_endpoints, in_closed_rect in Hpbox.
    change
      ((Rmin (fst (init s)) (fst (term s)) <= fst p <=
          Rmax (fst (init s)) (fst (term s))) /\
       (Rmin (snd (init s)) (snd (term s)) <= snd p <=
          Rmax (snd (init s)) (snd (term s)))) in Hpbox.
    exact (proj2 Hpbox). }
  assert (Havoid := sparse_nonadjacent_box_avoids_sub_points
                       l sub r s q Hsparse Hs Hq).
  split; apply Rnot_lt_le; intro Hend.
  - apply Havoid.
    unfold in_segment_rect_or_endpoints, in_closed_rect, rect_of; simpl.
    split; [lra |].
    destruct Hpy as [Hpy0 Hpy1].
    split.
    + eapply Rle_trans; [exact Hpy0 | apply Rlt_le; exact Hy].
    + eapply Rle_trans; [exact Hqhi |].
      eapply Rle_trans; [apply Rlt_le; exact Hend | apply Rmax_l].
  - apply Havoid.
    unfold in_segment_rect_or_endpoints, in_closed_rect, rect_of; simpl.
    split; [lra |].
    destruct Hpy as [Hpy0 Hpy1].
    split.
    + eapply Rle_trans; [exact Hpy0 | apply Rlt_le; exact Hy].
    + eapply Rle_trans; [exact Hqhi |].
      eapply Rle_trans; [apply Rlt_le; exact Hend | apply Rmax_r].
Qed.

(* x 範囲内の端点には classified_*_bbox を使う。範囲外の端点を
   含む場合は、端点長方形が sub を横切れば sparse に反する。 *)
Lemma operated_nonadjacent_endpoints_separated_from_spec :
  forall l sub r h s,
    sub <> [] ->
    connected sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    ClassificationSpec l sub r ->
    In s (nonadjacent_sides l r) ->
    endpoint_box_separated_from_sub sub
      (operate_point l sub r h (init s))
      (operate_point l sub r h (term s)).
Proof.
  intros l sub r h s Hne Hconn Hh Hsparse Hspec Hs.
  destruct (classic (both_left_of_sub sub (init s) (term s)))
    as [Hleft | Hleft].
  - right; right; left. unfold both_left_of_sub in *.
    now rewrite !operate_point_fst.
  - destruct (classic (both_right_of_sub sub (init s) (term s)))
      as [Hright | Hright].
    + right; right; right. unfold both_right_of_sub in *.
      now rewrite !operate_point_fst.
    + destruct (nonhorizontal_sides_have_common_x
                  sub s Hleft Hright)
        as [x [Hsubx Hsegx]].
      destruct (segment_has_point_at_x s x ltac:(lra))
        as [p [Hp Hpx]].
      destruct (connected_sub_has_point_at_x sub x Hne Hconn ltac:(lra))
        as [q [Hq Hqx]].
      assert (Hprange : in_sub_x_range sub p).
      { unfold in_sub_x_range. rewrite Hpx. lra. }
      assert (Hsamex : fst p = fst q) by lra.
      assert (Hpneq : p <> q).
      { intro Heq. subst q.
        apply (sparse_nonadjacent_box_avoids_sub_points
                 l sub r s p Hsparse Hs Hq).
        now apply segment_in_rect_or_endpoints. }
      pose proof (classified_segment_at_sub_x
                    l sub r
                    Hspec
                    s p Hs Hp Hprange) as [Hup Hdown].
      assert (Hy : snd q < snd p \/ snd p < snd q).
      { destruct (total_order_T (snd q) (snd p))
          as [[Hlt | Heq] | Hgt].
        - now left.
        - exfalso. apply Hpneq.
          destruct p as [xp yp], q as [xq yq].
          simpl in Hsamex, Heq |- *. f_equal; lra.
        - now right. }
      assert (Hqsegx :
          rx0 (rect_of [s]) <= fst q <= rx1 (rect_of [s])) by lra.
      destruct Hy as [Hy | Hy].
      * assert (Habove : above_sub_at_x sub p).
        { exists q. repeat split; assumption. }
        destruct (Hup Habove) as [Hinit Hterm].
        pose proof (above_sub_point_bounds_segment_endpoints
                      l sub r s p q Hsparse Hs Hp Hq Hqsegx Hy)
          as [HinitY HtermY].
        left. unfold both_above_of_sub, operate_point, shift.
        rewrite Hinit, Hterm. simpl.
        unfold h_large, rect_height in Hh. lra.
      * assert (Hbelow : below_sub_at_x sub p).
        { exists q. repeat split; assumption. }
        destruct (Hdown Hbelow) as [Hinit Hterm].
        pose proof (below_sub_point_bounds_segment_endpoints
                      l sub r s p q Hsparse Hs Hp Hq Hqsegx Hy)
          as [HinitY HtermY].
        right; left. unfold both_below_of_sub, operate_point, shift.
        rewrite Hinit, Hterm. simpl.
        unfold h_large, rect_height in Hh. lra.
Qed.

Lemma in_rect_or_endpoints_at_closed_bounds :
  forall old p,
    in_rect_or_endpoints_at old p ->
    rx0 (rect_of old) <= fst p <= rx1 (rect_of old)
    /\ ry0 (rect_of old) <= snd p <= ry1 (rect_of old).
Proof.
  intros old p Hp. exact Hp.
Qed.

Lemma in_sub_rect_or_endpoints_bbox_y :
  forall sub p,
    sub <> [] ->
    in_rect_or_endpoints_at sub p ->
    ry0 (bbox_of sub) <= snd p <= ry1 (bbox_of sub).
Proof.
  intros sub p Hne Hp.
  pose proof (bbox_of_bounds sub (init (hd_segment sub))
                (onSegmentlist_init_hd sub Hne)) as Hinit.
  pose proof (bbox_of_bounds sub (term (last_segment sub))
                (onSegmentlist_term_last sub Hne)) as Hterm.
  pose proof (in_rect_or_endpoints_at_closed_bounds sub p Hp) as [_ Hy].
  assert (Hlo : ry0 (bbox_of sub) <= ry0 (rect_of sub)).
  { unfold rect_of; simpl. apply Rmin_glb; lra. }
  assert (Hhi : ry1 (rect_of sub) <= ry1 (bbox_of sub)).
  { unfold rect_of; simpl. apply Rmax_lub; lra. }
  lra.
Qed.

(* 二端点の閉長方形が sub の上下左右のいずれかに厳密に離れていれば、
   その中に収まるセグメントも sub の閉長方形を避ける。 *)
Lemma separated_endpoint_box_avoids_sub :
  forall sub s p,
    sub <> [] ->
    endpoint_box_separated_from_sub sub (init s) (term s) ->
    in_segment_rect_or_endpoints s p ->
    ~ in_rect_or_endpoints_at sub p.
Proof.
  intros sub s p Hne Hsep Hp Hsub.
  pose proof (in_segment_rect_or_endpoints_closed_bounds s p Hp)
    as [[Hpx0 Hpx1] [Hpy0 Hpy1]].
  pose proof (in_sub_rect_or_endpoints_bbox_y sub p Hne Hsub)
    as [Hsy0 Hsy1].
  pose proof (in_rect_or_endpoints_at_closed_bounds sub p Hsub)
    as [[Hsx0 Hsx1] _].
  destruct Hsep as [Habove | [Hbelow | [Hleft | Hright]]].
  - unfold both_above_of_sub in Habove.
    destruct Habove as [Hinit' Hterm'].
    change (Rmin (snd (init s)) (snd (term s)) <= snd p) in Hpy0.
    pose proof (Rmin_glb_lt _ _ _ Hinit' Hterm'). lra.
  - unfold both_below_of_sub in Hbelow.
    destruct Hbelow as [Hinit' Hterm'].
    change (snd p <= Rmax (snd (init s)) (snd (term s))) in Hpy1.
    pose proof (Rmax_lub_lt _ _ _ Hinit' Hterm'). lra.
  - unfold both_left_of_sub in Hleft.
    destruct Hleft as [Hinit' Hterm'].
    change (fst p <= Rmax (fst (init s)) (fst (term s))) in Hpx1.
    pose proof (Rmax_lub_lt _ _ _ Hinit' Hterm'). lra.
  - unfold both_right_of_sub in Hright.
    destruct Hright as [Hinit' Hterm'].
    change (Rmin (fst (init s)) (fst (term s)) <= fst p) in Hpx0.
    pose proof (Rmin_glb_lt _ _ _ Hinit' Hterm'). lra.
Qed.

(* [nonadjacent_sides] に現れるセグメントは、もとの三分割列に属する。 *)
Lemma nonadjacent_sides_in_whole :
  forall l sub r s,
    In s (nonadjacent_sides l r) ->
    In s (l ++ sub ++ r).
Proof.
  intros l sub r s Hs.
  unfold nonadjacent_sides in Hs. rewrite in_app_iff in Hs.
  destruct Hs as [Hl | Hr].
  - rewrite !in_app_iff. left.
    induction l as [|a l IH]; [contradiction|].
    destruct l as [|b l].
    + simpl in Hl. contradiction.
    + simpl in Hl |- *. destruct Hl as [<- | Hl].
      * now left.
      * right. apply IH. exact Hl.
  - rewrite !in_app_iff. right; right.
    destruct r as [|a r]; [simpl in Hr; contradiction|].
    simpl in Hr |- *. now right.
Qed.

(* strict 延長線の基点分類と h_large から，移動後の
   延長線点が sub の閉長方形へ入らないことを導く。 *)
Lemma classified_shifted_extension_avoids_sub_rect_from_spec :
  forall l sub r h p q g,
    sub <> [] ->
    connected sub ->
    ClassificationSpec l sub r ->
    h_large h sub ->
    (onHead_extend_strict (l ++ sub ++ r) q
     \/ onLast_extend_strict (l ++ sub ++ r) q) ->
    (g = RegUp -> forall z,
      onSegmentlist sub z ->
      fst q = fst z -> snd q < snd z -> classify l sub r z = RegUp) ->
    (g = RegDown -> forall z,
      onSegmentlist sub z ->
      fst q = fst z -> snd z < snd q -> classify l sub r z = RegDown) ->
    (rx0 (rect_of sub) <= fst q <= rx1 (rect_of sub) ->
      g = RegUp \/ g = RegDown) ->
    p = shift h g q ->
    ~ in_rect_or_endpoints_at sub p.
Proof.
  intros l sub r h p q g Hne Hconn Hspec Hh Hqextend
    Habove Hbelow Hinside Hshift HpSub.
  pose proof (in_rect_or_endpoints_at_closed_bounds sub p HpSub)
    as [Hpx _].
  pose proof (in_sub_rect_or_endpoints_bbox_y sub p Hne HpSub)
    as Hpy.
  assert (Hxpq : fst p = fst q).
  { rewrite Hshift, shift_fst. reflexivity. }
  destruct (connected_sub_has_point_at_x sub (fst p) Hne Hconn Hpx)
    as [z [Hz Hxz]].
  pose proof (bbox_of_bounds sub z Hz) as Hzy.
  pose proof (classified_sub_fixed l sub r Hspec z Hz) as Hzfix.
  destruct g.
  - simpl in Hshift. subst p.
    destruct (Hinside Hpx); discriminate.
  - assert (Hqz : snd q < snd z).
    { pose proof (f_equal snd Hshift) as Hyshift.
      simpl in Hyshift. unfold h_large, rect_height in Hh. lra. }
    pose proof (Habove eq_refl z Hz ltac:(lra) Hqz) as Hzup.
    congruence.
  - assert (Hzq : snd z < snd q).
    { pose proof (f_equal snd Hshift) as Hyshift.
      simpl in Hyshift. unfold h_large, rect_height in Hh. lra. }
    pose proof (Hbelow eq_refl z Hz ltac:(lra) Hzq) as Hzdown.
    congruence.
Qed.

(* 埋め込まれた隣接セグメントは共有接続点でしか交わらない。 *)
Lemma embedded_adjacent_positive_bodies_disjoint :
  forall ds ls i s t u v,
    embed_listDir ds ls ->
    nth_error ls i = Some s ->
    nth_error ls (S i) = Some t ->
    0 < u <= 1 ->
    0 < v <= 1 ->
    point s u <> point t v.
Proof.
  intros ds ls i s t u v [sc [_ Hembed]] Hs Ht Hu Hv Heq.
  destruct (embed_scurve_adjacent_data sc ls i s t Hembed Hs Ht)
    as [ps [pt [Hsemb [Htemb [Hdc Hjoin]]]]].
  assert (Hons : onSegment s (point s u)).
  { exists u. split; [lra | reflexivity]. }
  assert (Hont : onSegment t (point s u)).
  { exists v. split; [lra | now symmetry]. }
  pose proof (adjacent_not_intersect_except_junction
                ps pt s t (point s u) Hdc Hsemb Htemb Hjoin Hons Hont)
    as Hj.
  assert (Hv0 : v = 0).
  { apply (point_injective t).
    change (point t v = init t).
    rewrite <- Hjoin, <- Hj. now symmetry. }
  lra.
Qed.

(* 非隣接部分を幾何学的に排除できれば、隣接部分は上の補題で補われ、
   全ての異なる出現の正パラメータ本体が非交差になる。 *)
Lemma nonadjacent_and_embedded_give_positive_bodies_disjoint :
  forall ds ls,
    embed_listDir ds ls ->
    nonadjacent_bodies_disjoint ls ->
    positive_bodies_disjoint ls.
Proof.
  intros ds ls Hembed Hfar i j s t u v Hs Ht Hij Hu Hv Heq.
  destruct (Nat.lt_trichotomy i j) as [Hijlt | [-> | Hjilt]].
  - destruct (Nat.eq_dec j (S i)) as [-> | Hnotadj].
    + exact (embedded_adjacent_positive_bodies_disjoint
               ds ls i s t u v Hembed Hs Ht Hu Hv Heq).
    + eapply (Hfar i j s t (point s u)); eauto.
      * left. lia.
      * exists u. split; [lra | reflexivity].
      * exists v. split; [lra | now symmetry].
  - contradiction.
  - destruct (Nat.eq_dec i (S j)) as [-> | Hnotadj].
    + exact (embedded_adjacent_positive_bodies_disjoint
               ds ls j t s v u Hembed Ht Hs Hv Hu (eq_sym Heq)).
    + eapply (Hfar i j s t (point s u)); eauto.
      * right. lia.
      * exists u. split; [lra | reflexivity].
      * exists v. split; [lra | now symmetry].
Qed.

End PreparedReconnect.
