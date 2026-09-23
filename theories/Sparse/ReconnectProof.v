Require Export Sparse.ReconnectSplit.
Require Import Stdlib.Logic.ClassicalDescription.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.

(* 蓋として現れる先頭・末尾セグメントの向きを隣接関係から取り出す。 *)
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

(* 左側の戻り蓋の二形は、蓋判定には含めず、sub との [dc] から導く。 *)
Lemma terminal_lid_shape_from_dc :
  forall ds l sub r,
    sub <> [] ->
    x_monotone_segs sub ->
    embed_listDir ds (l ++ sub ++ r) ->
    terminal_lid l ->
    embed (n, w, cc) (last_segment l)
    \/ embed (s, w, cx) (last_segment l).
Proof.
  intros ds l sub r Hsub Hmono Hembed [Hl Hwest].
  assert (Htail : sub ++ r <> []) by (destruct sub; contradiction || discriminate).
  assert (Hembed' : embed_listDir ds (l ++ (sub ++ r))).
  { exact Hembed. }
  destruct (embed_listDir_app_boundary_data
              ds l (sub ++ r) Hl Htail Hembed')
    as [ps1 [ps2 [Hemb1 [Hemb2 [Hdc _]]]]].
  assert (Hhead : hd_segment (sub ++ r) = hd_segment sub).
  { symmetry. unfold hd_segment. now apply hd_app. }
  rewrite Hhead in Hemb2.
  assert (Heast : fst (init (hd_segment sub)) < fst (term (hd_segment sub))).
  { apply Hmono. destruct sub; [contradiction | now left]. }
  exact (proj1 (west_to_east_dc_shapes
                  (last_segment l) (hd_segment sub) ps1 ps2
                  Hemb1 Hemb2 Hdc Hwest Heast)).
Qed.

(* 右側の戻り蓋については、sub の末尾からの [dc] が双対の二形を与える。 *)
Lemma initial_lid_shape_from_dc :
  forall ds l sub r,
    sub <> [] ->
    x_monotone_segs sub ->
    embed_listDir ds (l ++ sub ++ r) ->
    initial_lid r ->
    embed (n, w, cx) (hd_segment r)
    \/ embed (s, w, cc) (hd_segment r).
Proof.
  intros ds l sub r Hsub Hmono Hembed [Hr Hwest].
  assert (Hprefix : l ++ sub <> []).
  { intros Hnil. apply app_eq_nil in Hnil as [_ Hnil]. contradiction. }
  assert (Hembed' : embed_listDir ds ((l ++ sub) ++ r)).
  { rewrite <- app_assoc. exact Hembed. }
  destruct (embed_listDir_app_boundary_data
              ds (l ++ sub) r Hprefix Hr Hembed')
    as [ps1 [ps2 [Hemb1 [Hemb2 [Hdc _]]]]].
  assert (Hlast : last_segment (l ++ sub) = last_segment sub).
  { now apply last_app_nonnil. }
  rewrite Hlast in Hemb1.
  assert (Heast : fst (init (last_segment sub)) < fst (term (last_segment sub))).
  { apply Hmono. apply last_In. exact Hsub. }
  exact (proj2 (east_to_west_dc_shapes
                  (last_segment sub) (hd_segment r) ps1 ps2
                  Hemb1 Hemb2 Hdc Heast Hwest)).
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

Lemma reconnect_head_init_slope_after :
  forall ds l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    0 <= h ->
    l <> [] ->
    reconnect_init_slope_after l sub r h (hd_segment l).
Proof.
  intros ds l sub r h Hne Hconn Hmono Hsparse Hembed Hext Hh Hl.
  unfold reconnect_init_slope_after, operate_point.
  exact (classified_head_init_slope_reconnectable
           l sub r
           (classify_spec l sub r Hne Hmono Hsparse
              (ex_intro _ ds Hembed) Hext)
           h Hh Hl).
Qed.

Lemma reconnect_last_term_slope_after :
  forall ds l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    0 <= h ->
    r <> [] ->
    reconnect_term_slope_after l sub r h (last_segment r).
Proof.
  intros ds l sub r h Hne Hconn Hmono Hsparse Hembed Hext Hh Hr.
  unfold reconnect_term_slope_after, operate_point.
  exact (classified_last_term_slope_reconnectable
           l sub r
           (classify_spec l sub r Hne Hmono Hsparse
              (ex_intro _ ds Hembed) Hext)
           h Hh Hr).
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
Lemma reconnect_head_extension_preimage :
  forall l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    (l <> [] -> reconnect_init_slope_after l sub r h (hd_segment l)) ->
    onHead_extend (ordinary_reconnect_split l sub r h) p ->
    exists q,
      onHead_extend (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (init (hd_segment (l ++ sub ++ r)))) q.
Proof.
  intros l sub r h p Hne Hconn Hmono Hsparse Hwhole Hembedded Hext Hslope Hp.
  destruct l as [|a l'].
  - destruct sub as [|b sub']; [contradiction|].
    assert (Hfix : classify [] (b :: sub') r (init b) = RegFix).
    { apply (classified_sub_fixed
               [] (b :: sub') r
               (classify_spec [] (b :: sub') r
                  ltac:(discriminate) Hmono Hsparse Hembedded Hext)).
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
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    (r <> [] -> reconnect_term_slope_after l sub r h (last_segment r)) ->
    onLast_extend (ordinary_reconnect_split l sub r h) p ->
    exists q,
      onLast_extend (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (term (last_segment (l ++ sub ++ r)))) q.
Proof.
  intros l sub r h p Hne Hconn Hmono Hsparse Hwhole Hembedded Hext Hslope Hp.
  destruct r as [|a r'].
  - assert (HoldLast : last_segment (l ++ sub ++ []) = last_segment sub).
    { rewrite app_nil_r. apply last_app_nonnil. exact Hne. }
    assert (HnewLast :
      last_segment (ordinary_reconnect_split l sub [] h) = last_segment sub).
    { unfold ordinary_reconnect_split, reconnect_segs. simpl. rewrite app_nil_r.
      apply last_app_nonnil. exact Hne. }
    assert (Hfix : classify l sub [] (term (last_segment sub)) = RegFix).
    { apply (classified_sub_fixed
               l sub []
               (classify_spec l sub [] Hne Hmono Hsparse Hembedded Hext)).
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
Lemma reconnect_head_strict_extension_preimage :
  forall ds l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    0 <= h ->
    onHead_extend_strict (ordinary_reconnect_split l sub r h) p ->
    exists q,
      onHead_extend_strict (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (init (hd_segment (l ++ sub ++ r)))) q.
Proof.
  intros ds l sub r h p Hne Hconn Hmono Hsparse Hembed Hext Hh Hstrict.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  destruct l as [|a l'].
  - destruct sub as [|b sub']; [contradiction|].
    assert (Hfix : classify [] (b :: sub') r (init b) = RegFix).
    { apply (classified_sub_fixed
               [] (b :: sub') r
               (classify_spec [] (b :: sub') r
                  ltac:(discriminate) Hmono Hsparse
                  (ex_intro _ ds Hembed) Hext)).
      apply onSegmentlist_init_hd. discriminate. }
    exists p. split.
    + exact Hstrict.
    + simpl in Hfix |- *. now rewrite Hfix.
  - simpl in Hstrict |- *.
    destruct Hstrict as [t [Ht Hpoint]].
    change (point (reconnect_one (a :: l') sub r h a) t = p) in Hpoint.
    pose proof (reconnect_head_init_slope_after
                  ds (a :: l') sub r h Hne Hconn Hmono Hsparse Hembed Hext Hh
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
Lemma reconnect_last_strict_extension_preimage :
  forall ds l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    0 <= h ->
    onLast_extend_strict (ordinary_reconnect_split l sub r h) p ->
    exists q,
      onLast_extend_strict (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (term (last_segment (l ++ sub ++ r)))) q.
Proof.
  intros ds l sub r h p Hne Hconn Hmono Hsparse Hembed Hext Hh Hstrict.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  destruct r as [|a r'].
  - assert (HoldLast : last_segment (l ++ sub ++ []) = last_segment sub).
    { rewrite app_nil_r. apply last_app_nonnil. exact Hne. }
    assert (HnewLast :
      last_segment (ordinary_reconnect_split l sub [] h) = last_segment sub).
    { unfold ordinary_reconnect_split, reconnect_segs. simpl. rewrite app_nil_r.
      apply last_app_nonnil. exact Hne. }
    assert (Hfix : classify l sub [] (term (last_segment sub)) = RegFix).
    { apply (classified_sub_fixed
               l sub []
               (classify_spec l sub [] Hne Hmono Hsparse
                  (ex_intro _ ds Hembed) Hext)).
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
    pose proof (reconnect_last_term_slope_after
                  ds l sub (a :: r') h Hne Hconn Hmono Hsparse Hembed Hext Hh
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


(* 疎性と延長線を保つ再接続。 *)

(* sub に隣接する l 末尾より下の端点は、分類移動後にもその旧長方形
   より下に残る。隣接・非隣接の区別は不要である。 *)
Lemma operated_endpoint_below_terminal_stays_below :
  forall l sub r h p,
    sub <> [] ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    0 <= h ->
    l <> [] ->
    ~ terminal_lid l ->
    endpoint_of (l ++ sub ++ r) p ->
    snd p < ry0 (rect_of [last_segment l]) ->
    snd (operate_point l sub r h p) < ry0 (rect_of [last_segment l]).
Proof.
  intros l sub r h p Hne Hmono Hsparse Hembed Hext Hh Hl HnotLid Hp Hbelow.
  unfold operate_point.
  pose proof (classified_below_terminal_not_up
                l sub r
                (classify_spec l sub r Hne Hmono Hsparse Hembed Hext)
                Hl HnotLid p Hp Hbelow) as HnotUp.
  pose proof (shift_not_up_nonincreasing
                h (classify l sub r p) p Hh HnotUp).
  lra.
Qed.

(* r 先頭についての双対。 *)
Lemma operated_endpoint_below_initial_stays_below :
  forall l sub r h p,
    sub <> [] ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    0 <= h ->
    r <> [] ->
    ~ initial_lid r ->
    endpoint_of (l ++ sub ++ r) p ->
    snd p < ry0 (rect_of [hd_segment r]) ->
    snd (operate_point l sub r h p) < ry0 (rect_of [hd_segment r]).
Proof.
  intros l sub r h p Hne Hmono Hsparse Hembed Hext Hh Hr HnotLid Hp Hbelow.
  unfold operate_point.
  pose proof (classified_below_initial_not_up
                l sub r
                (classify_spec l sub r Hne Hmono Hsparse Hembed Hext)
                Hr HnotLid p Hp Hbelow) as HnotUp.
  pose proof (shift_not_up_nonincreasing
                h (classify l sub r p) p Hh HnotUp).
  lra.
Qed.

(* 十分大きい移動では、各セグメントの二端点の y 座標は一致しない。 *)
Lemma operation_height_safe :
  forall l sub r h s,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    In s (l ++ sub ++ r) ->
    snd (operate_point l sub r h (init s)) <>
    snd (operate_point l sub r h (term s)).
Proof.
  intros l sub r h s Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hs.
  pose proof (classified_segment_endpoints_monotone
                l sub r
                (classify_spec l sub r Hne Hmono Hsparse Hembedded Hext)
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

(* 一つのセグメントについて、分類された両端点を元の向きで再接続できる。 *)
Lemma operate_one_endpoints_reconnectable :
  forall l sub r h s,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    In s (l ++ sub ++ r) ->
    reconnectable_after l sub r h s.
Proof.
  intros l sub r h s Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hs.
  unfold reconnectable_after, reconnectable. split.
  - rewrite !operate_point_fst. apply neq_init_term_x.
  - eapply operation_height_safe; eauto.
Qed.

Lemma operate_endpoints_reconnectable :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r).
Proof.
  intros l sub r h Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext s Hs.
  now apply (operate_one_endpoints_reconnectable
               l sub r h s Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext).
Qed.

(* 左蓋の安全再接続。将来は l/sub/r 非依存の safe-corridor における
   始点傾き保存再接続定理から導く。 *)
Lemma choose_terminal_lid_spec :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    terminal_lid l ->
    terminal_lid_reconnect_spec l sub r h (last_segment l)
      (terminal_lid_blockers l sub r h)
      (choose_terminal_lid l sub r h).
Admitted.

(* 右蓋の双対。終点傾きを保存する safe-corridor 定理から導く予定。 *)
Lemma choose_initial_lid_spec :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    initial_lid r ->
    initial_lid_reconnect_spec l sub r h (hd_segment r)
      (initial_lid_blockers l sub r h)
      (choose_initial_lid l sub r h).
Admitted.

Lemma removelast_length_nonempty : forall (A : Type) (xs : list A),
  xs <> [] -> S (length (removelast xs)) = length xs.
Proof.
  intros A xs. induction xs as [|x xs IH]; [contradiction |].
  destruct xs as [|y ys].
  - reflexivity.
  - simpl. intros _. specialize (IH ltac:(discriminate)). simpl in IH. lia.
Qed.

Lemma reconnect_left_terminal_eq : forall l sub r h,
  terminal_lid l ->
  reconnect_left l sub r h =
    removelast (reconnect_segs l sub r h l) ++
      [choose_terminal_lid l sub r h].
Proof.
  intros l sub r h Hlid. unfold reconnect_left.
  destruct (excluded_middle_informative (terminal_lid l));
    [reflexivity | contradiction].
Qed.

Lemma reconnect_left_nonterminal_eq : forall l sub r h,
  ~ terminal_lid l ->
  reconnect_left l sub r h = reconnect_segs l sub r h l.
Proof.
  intros l sub r h Hlid. unfold reconnect_left.
  destruct (excluded_middle_informative (terminal_lid l));
    [contradiction | reflexivity].
Qed.

Lemma reconnect_right_initial_eq : forall l sub r h,
  initial_lid r ->
  reconnect_right l sub r h =
    choose_initial_lid l sub r h :: tl (reconnect_segs l sub r h r).
Proof.
  intros l sub r h Hlid. unfold reconnect_right.
  destruct (excluded_middle_informative (initial_lid r));
    [reflexivity | contradiction].
Qed.

Lemma reconnect_right_noninitial_eq : forall l sub r h,
  ~ initial_lid r ->
  reconnect_right l sub r h = reconnect_segs l sub r h r.
Proof.
  intros l sub r h Hlid. unfold reconnect_right.
  destruct (excluded_middle_informative (initial_lid r));
    [contradiction | reflexivity].
Qed.

Lemma reconnect_left_length : forall l sub r h,
  length (reconnect_left l sub r h) = length l.
Proof.
  intros l sub r h. unfold reconnect_left.
  destruct (excluded_middle_informative (terminal_lid l)) as [Hlid | Hlid].
  - rewrite length_app. simpl.
    pose proof (removelast_length_nonempty
                  Segment (reconnect_segs l sub r h l)) as Hlen.
    assert (Hmap : reconnect_segs l sub r h l <> []).
    { intros Hnil. apply (proj1 Hlid).
      apply length_zero_iff_nil.
      pose proof (f_equal (@length Segment) Hnil) as Hlen0.
      rewrite reconnect_segs_length in Hlen0. exact Hlen0. }
    specialize (Hlen Hmap). rewrite reconnect_segs_length in Hlen. lia.
  - apply reconnect_segs_length.
Qed.

Lemma reconnect_right_length : forall l sub r h,
  length (reconnect_right l sub r h) = length r.
Proof.
  intros l sub r h. unfold reconnect_right.
  destruct (excluded_middle_informative (initial_lid r)) as [Hlid | Hlid].
  - destruct r as [|s r].
    + exfalso. apply (proj1 Hlid). reflexivity.
    + simpl. rewrite reconnect_segs_length. reflexivity.
  - apply reconnect_segs_length.
Qed.

Lemma reconnect_split_safe_length : forall l sub r h,
  length (reconnect_split l sub r h) = length (l ++ sub ++ r).
Proof.
  intros. unfold reconnect_split. repeat rewrite length_app.
  rewrite reconnect_left_length, reconnect_right_length. reflexivity.
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

Lemma same_segment_box_contains : forall s t p,
  same_segment_box s t ->
  in_segment_rect_or_endpoints s p ->
  in_segment_rect_or_endpoints t p.
Proof.
  intros s t p Hbox Hp.
  unfold in_segment_rect_or_endpoints in *.
  now rewrite <- (same_segment_box_rect s t Hbox).
Qed.

(* sub に隣接する二つの蓋は [nonadjacent_sides] から除かれるので、
   sub 周りで検査する安全版の列は通常再接続版と完全に一致する。 *)
Lemma safe_nonadjacent_sides_eq_ordinary : forall l sub r h,
  nonadjacent_sides
    (reconnect_left l sub r h)
    (reconnect_right l sub r h)
  =
  nonadjacent_sides
    (reconnect_segs l sub r h l)
    (reconnect_segs l sub r h r).
Proof.
  intros l sub r h.
  unfold nonadjacent_sides, reconnect_left, reconnect_right.
  destruct (excluded_middle_informative (terminal_lid l)) as [Hleft | Hleft];
  destruct (excluded_middle_informative (initial_lid r)) as [Hright | Hright].
  - rewrite removelast_last.
    destruct r as [|s r].
    + exfalso. apply (proj1 Hright). reflexivity.
    + simpl. reflexivity.
  - rewrite removelast_last. reflexivity.
  - destruct r as [|s r].
    + exfalso. apply (proj1 Hright). reflexivity.
    + simpl. reflexivity.
  - reflexivity.
Qed.

(* 安全版で変更し得る左蓋が列の先頭でもあるのは [l] が singleton の
   場合だけであり、その場合も始点と始点傾きが通常版と一致する。 *)
Lemma safe_head_extension_iff_ordinary :
  forall ds l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    onHead_extend (reconnect_split l sub r h) p <->
    onHead_extend (ordinary_reconnect_split l sub r h) p.
Proof.
  intros ds l sub r h p Hne Hconn Hmono Hh Hsparse Hembed Hext.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { now apply (embed_listDir_connected ds (l ++ sub ++ r)). }
  destruct l as [|a [|b l']].
  - destruct sub as [|s sub']; [contradiction |].
    unfold reconnect_split, ordinary_reconnect_split, reconnect_left,
      reconnect_right, reconnect_segs, onHead_extend, hd_segment.
    destruct (excluded_middle_informative (terminal_lid [])) as [Hlid | Hlid].
    + exfalso. apply (proj1 Hlid). reflexivity.
    + simpl. reflexivity.
  - unfold reconnect_split, ordinary_reconnect_split, reconnect_left,
      reconnect_segs, onHead_extend, hd_segment.
    destruct (excluded_middle_informative (terminal_lid [a])) as [Hlid | Hlid].
    2: simpl; reflexivity.
    simpl.
    pose proof (choose_terminal_lid_spec
                  [a] sub r h Hne Hconn Hmono Hh Hsparse Hwhole
                  (ex_intro _ ds Hembed) Hext Hlid) as Hchosen.
    unfold terminal_lid_reconnect_spec in Hchosen.
    destruct Hchosen as [HchosenRec [HchosenSlope _]].
    assert (HaIn : In a ([a] ++ sub ++ r)) by (simpl; auto).
    assert (HaRec : reconnectable_after [a] sub r h a).
    { eapply operate_one_endpoints_reconnectable; eauto. }
    assert (Hinit :
      init (choose_terminal_lid [a] sub r h) =
      init (reconnect_one [a] sub r h a)).
    { unfold reconnects_after in HchosenRec.
      rewrite (proj1 HchosenRec).
      symmetry. now apply reconnect_one_init. }
    assert (Hslope :
      slope_init (choose_terminal_lid [a] sub r h) =
      slope_init (reconnect_one [a] sub r h a)).
    { rewrite HchosenSlope.
      symmetry. eapply reconnect_one_head_slope_init.
      + discriminate.
      + reflexivity.
      + exact (reconnect_head_init_slope_after
                 ds [a] sub r h Hne Hconn Hmono Hsparse Hembed Hext
                 (Rlt_le _ _ (proj1 Hh)) ltac:(discriminate)). }
    exact (head_extension_determined_by_init_slope
             (choose_terminal_lid [a] sub r h)
             (reconnect_one [a] sub r h a) Hinit Hslope p).
  - unfold reconnect_split, ordinary_reconnect_split, reconnect_left,
      reconnect_segs, onHead_extend, hd_segment.
    destruct (excluded_middle_informative (terminal_lid (a :: b :: l')));
      simpl; reflexivity.
Qed.

(* 右側についての双対。安全な右蓋が列の末尾でもある singleton の
   場合には、終点と終点傾きの保存から延長線の一致を得る。 *)
Lemma safe_last_extension_iff_ordinary :
  forall ds l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    onLast_extend (reconnect_split l sub r h) p <->
    onLast_extend (ordinary_reconnect_split l sub r h) p.
Proof.
  intros ds l sub r h p Hne Hconn Hmono Hh Hsparse Hembed Hext.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { now apply (embed_listDir_connected ds (l ++ sub ++ r)). }
  destruct r as [|a [|b r']].
  - assert (HsafeLast :
        last_segment (reconnect_split l sub [] h) = last_segment sub).
    { unfold reconnect_split, reconnect_right.
      destruct (excluded_middle_informative (initial_lid [])) as [Hlid | Hlid].
      - exfalso. apply (proj1 Hlid). reflexivity.
      - simpl. rewrite app_nil_r. now apply last_app_nonnil. }
    assert (HordinaryLast :
        last_segment (ordinary_reconnect_split l sub [] h) = last_segment sub).
    { unfold ordinary_reconnect_split, reconnect_segs. simpl.
      rewrite app_nil_r. now apply last_app_nonnil. }
    unfold onLast_extend. now rewrite HsafeLast, HordinaryLast.
  - unfold onLast_extend.
    destruct (excluded_middle_informative (initial_lid [a])) as [Hlid | Hlid].
    2: {
      assert (HsafeLast :
          last_segment (reconnect_split l sub [a] h) =
          reconnect_one l sub [a] h a).
      { unfold reconnect_split.
        rewrite (last_app_nonnil (reconnect_left l sub [a] h)
                   (sub ++ reconnect_right l sub [a] h)) by
          (destruct sub; [contradiction | discriminate]).
        rewrite (last_app_nonnil sub (reconnect_right l sub [a] h)).
        - unfold reconnect_right, reconnect_segs.
          destruct (excluded_middle_informative (initial_lid [a]));
            [contradiction | reflexivity].
        - unfold reconnect_right.
          destruct (excluded_middle_informative (initial_lid [a]));
            [contradiction | discriminate]. }
      assert (HordinaryLast :
          last_segment (ordinary_reconnect_split l sub [a] h) =
          reconnect_one l sub [a] h a).
      { unfold ordinary_reconnect_split, reconnect_segs.
        transitivity
          (last_segment (sub ++ [reconnect_one l sub [a] h a])).
        - apply last_app_nonnil. destruct sub; [contradiction | discriminate].
        - transitivity (last_segment [reconnect_one l sub [a] h a]).
          + apply last_app_nonnil. discriminate.
          + reflexivity. }
      now rewrite HsafeLast, HordinaryLast. }
    assert (HsafeLast :
        last_segment (reconnect_split l sub [a] h) =
        choose_initial_lid l sub [a] h).
    { unfold reconnect_split.
      rewrite (last_app_nonnil (reconnect_left l sub [a] h)
                 (sub ++ reconnect_right l sub [a] h)) by
        (destruct sub; [contradiction | discriminate]).
      rewrite (last_app_nonnil sub (reconnect_right l sub [a] h)).
      - unfold reconnect_right.
        destruct (excluded_middle_informative (initial_lid [a]));
          [reflexivity | contradiction].
      - unfold reconnect_right.
        destruct (excluded_middle_informative (initial_lid [a]));
          [discriminate | contradiction]. }
    assert (HordinaryLast :
        last_segment (ordinary_reconnect_split l sub [a] h) =
        reconnect_one l sub [a] h a).
    { unfold ordinary_reconnect_split, reconnect_segs.
      transitivity
        (last_segment (sub ++ [reconnect_one l sub [a] h a])).
      - apply last_app_nonnil. destruct sub; [contradiction | discriminate].
      - transitivity (last_segment [reconnect_one l sub [a] h a]).
        + apply last_app_nonnil. destruct sub; discriminate.
        + reflexivity. }
    rewrite HsafeLast, HordinaryLast.
    pose proof (choose_initial_lid_spec
                  l sub [a] h Hne Hconn Hmono Hh Hsparse Hwhole
                  (ex_intro _ ds Hembed) Hext Hlid) as Hchosen.
    unfold initial_lid_reconnect_spec in Hchosen.
    destruct Hchosen as [HchosenRec [HchosenSlope _]].
    assert (HaIn : In a (l ++ sub ++ [a])).
    { apply in_or_app. right. apply in_or_app. right. now left. }
    assert (HaRec : reconnectable_after l sub [a] h a).
    { eapply operate_one_endpoints_reconnectable; eauto. }
    assert (Hterm :
      term (choose_initial_lid l sub [a] h) =
      term (reconnect_one l sub [a] h a)).
    { unfold reconnects_after in HchosenRec.
      rewrite (proj1 (proj2 HchosenRec)).
      symmetry. now apply reconnect_one_term. }
    assert (HnotHead : ~ head_init_slope_after l sub [a] h a).
    { unfold head_init_slope_after. intros [Hl [Heq _]].
      eapply (sparse_head_last_distinct_across_sub l sub [a]); eauto.
      now symmetry. }
    assert (Hslope :
      slope_term (choose_initial_lid l sub [a] h) =
      slope_term (reconnect_one l sub [a] h a)).
    { rewrite HchosenSlope.
      symmetry. eapply reconnect_one_last_slope_term.
      + exact HnotHead.
      + discriminate.
      + reflexivity.
      + exact (reconnect_last_term_slope_after
                 ds l sub [a] h Hne Hconn Hmono Hsparse Hembed Hext
                 (Rlt_le _ _ (proj1 Hh)) ltac:(discriminate)). }
    exact (last_extension_determined_by_term_slope
             (choose_initial_lid l sub [a] h)
             (reconnect_one l sub [a] h a) Hterm Hslope p).
  - unfold onLast_extend.
    set (f := reconnect_one l sub (a :: b :: r') h).
    assert (Htail : map f (b :: r') <> []) by discriminate.
    assert (HsafeLast :
        last_segment (reconnect_split l sub (a :: b :: r') h) =
        last_segment (map f (b :: r'))).
    { unfold reconnect_split, reconnect_right, reconnect_segs.
      destruct (excluded_middle_informative (initial_lid (a :: b :: r'))).
      - change
          (last_segment
             (reconnect_left l sub (a :: b :: r') h ++ sub ++
              choose_initial_lid l sub (a :: b :: r') h :: map f (b :: r')) =
           last_segment (map f (b :: r'))).
        transitivity
          (last_segment
             (sub ++ choose_initial_lid l sub (a :: b :: r') h ::
              map f (b :: r'))).
        + apply last_app_nonnil. destruct sub; discriminate.
        + transitivity
            (last_segment
               (choose_initial_lid l sub (a :: b :: r') h ::
                map f (b :: r'))).
          * apply last_app_nonnil. discriminate.
          * change
              (last_segment
                 ([choose_initial_lid l sub (a :: b :: r') h] ++
                  map f (b :: r')) =
               last_segment (map f (b :: r'))).
            apply last_app_nonnil. exact Htail.
      - change
          (last_segment
             (reconnect_left l sub (a :: b :: r') h ++ sub ++
              f a :: map f (b :: r')) =
           last_segment (map f (b :: r'))).
        transitivity (last_segment (sub ++ f a :: map f (b :: r'))).
        + apply last_app_nonnil. destruct sub; discriminate.
        + transitivity (last_segment (f a :: map f (b :: r'))).
          * apply last_app_nonnil. discriminate.
          * change
              (last_segment ([f a] ++ map f (b :: r')) =
               last_segment (map f (b :: r'))).
            apply last_app_nonnil. exact Htail. }
    assert (HordinaryLast :
        last_segment (ordinary_reconnect_split l sub (a :: b :: r') h) =
        last_segment (map f (b :: r'))).
    { unfold ordinary_reconnect_split, reconnect_segs.
      change
        (last_segment
           (map f l ++ sub ++ f a :: map f (b :: r')) =
         last_segment (map f (b :: r'))).
      transitivity (last_segment (sub ++ f a :: map f (b :: r'))).
      - apply last_app_nonnil. destruct sub; discriminate.
      - transitivity (last_segment (f a :: map f (b :: r'))).
        + apply last_app_nonnil. discriminate.
        + change
            (last_segment ([f a] ++ map f (b :: r')) =
             last_segment (map f (b :: r'))).
          apply last_app_nonnil. exact Htail. }
    now rewrite HsafeLast, HordinaryLast.
Qed.

(* 安全な蓋への置換後も、各位置の端点と向きは通常再接続と同じである。 *)
Lemma reconnect_left_reconnects_after :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    reconnects_list_after l sub r h l (reconnect_left l sub r h).
Proof.
  intros l sub r h Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hrec.
  unfold reconnect_left.
  destruct (excluded_middle_informative (terminal_lid l)) as [Hlid | Hlid].
  - destruct (exists_last (proj1 Hlid)) as [l0 [x Heq]].
    subst l.
    unfold reconnect_segs. rewrite map_app. simpl. rewrite removelast_last.
    apply Forall2_app.
    + apply reconnect_segs_reconnects_after.
      intros s Hs. apply Hrec. rewrite !in_app_iff. auto.
    + constructor; [|constructor].
      change (reconnects_after (l0 ++ [x]) sub r h x
        (choose_terminal_lid (l0 ++ [x]) sub r h)).
      pose proof (choose_terminal_lid_spec
                    (l0 ++ [x]) sub r h Hne Hconn Hmono Hh Hsparse
                    Hwhole Hembedded Hext Hlid) as Hchosen.
      rewrite (last_app_nonnil l0 [x]) in Hchosen by discriminate.
      simpl in Hchosen.
      exact (proj1 Hchosen).
  - apply reconnect_segs_reconnects_after.
    intros s Hs. apply Hrec. rewrite !in_app_iff. auto.
Qed.

Lemma reconnect_right_reconnects_after :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    reconnects_list_after l sub r h r (reconnect_right l sub r h).
Proof.
  intros l sub r h Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hrec.
  unfold reconnect_right.
  destruct (excluded_middle_informative (initial_lid r)) as [Hlid | Hlid].
  - destruct r as [|x r].
    + exfalso. apply (proj1 Hlid). reflexivity.
    + simpl. constructor.
      * change (reconnects_after l sub (x :: r) h x
          (choose_initial_lid l sub (x :: r) h)).
        pose proof (choose_initial_lid_spec
                      l sub (x :: r) h Hne Hconn Hmono Hh Hsparse
                      Hwhole Hembedded Hext Hlid) as Hchosen.
        exact (proj1 Hchosen).
      * change (reconnects_list_after l sub (x :: r) h r
          (reconnect_segs l sub (x :: r) h r)).
        apply reconnect_segs_reconnects_after.
        eapply all_reconnectable_mono; [exact Hrec |].
        intros s0 Hs0. rewrite !in_app_iff. simpl. tauto.
  - apply reconnect_segs_reconnects_after.
    intros s Hs. apply Hrec. rewrite !in_app_iff. auto.
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

(* 各位置で移動後の端点と向きを共有する列は、元と同じ向き列を埋め込む。 *)
Lemma reconnects_list_preserves_embed :
  forall l sub r h old new ds,
    reconnects_list_after l sub r h old new ->
    embed_listDir ds old ->
    embed_listDir ds new.
Proof.
  intros l sub r h old new ds Hrel Hembed.
  eapply embed_scurve_transfer; [exact Hembed | | |].
  - symmetry. now apply Forall2_length in Hrel.
  - intros i s s' Hold Hnew.
    pose proof (Forall2_nth_error_relation
                  Segment Segment (reconnects_after l sub r h)
                  old new Hrel i) as Hi.
    rewrite Hold, Hnew in Hi. exact (proj2 (proj2 Hi)).
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

(* 左右の安全な蓋と固定した sub を合わせても、全位置で再接続仕様を満たす。 *)
Lemma reconnect_split_reconnects_after :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    reconnects_list_after l sub r h (l ++ sub ++ r)
      (reconnect_split l sub r h).
Proof.
  intros l sub r h Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hrec.
  unfold reconnect_split.
  apply Forall2_app.
  - eapply reconnect_left_reconnects_after; eauto.
  - apply Forall2_app.
    + assert (Hsub : forall xs,
          (forall s, In s xs -> In s sub) ->
          reconnects_list_after l sub r h xs xs).
      { intros xs Hin. induction xs as [|s xs IH]; constructor.
        - unfold reconnects_after. repeat split; try reflexivity.
          + symmetry. apply operate_sub_endpoint.
            exists s. split; [apply Hin; now left | now left].
          + symmetry. apply operate_sub_endpoint.
            exists s. split; [apply Hin; now left | now right].
        - apply IH. intros t Ht. apply Hin. now right. }
      apply Hsub. auto.
    + eapply reconnect_right_reconnects_after; eauto.
Qed.

Lemma reconnect_split_safe_preserves_embed :
  forall l sub r h ds,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    embed_listDir ds (reconnect_split l sub r h).
Proof.
  intros l sub r h ds Hne Hconn Hmono Hh Hsparse Hwhole Hext Hrec Hembed.
  eapply reconnects_list_preserves_embed; [|exact Hembed].
  eapply reconnect_split_reconnects_after; eauto.
Qed.

(* split の同じ位置にある新旧セグメントは向きと operate 後の端点を共有する。 *)
Lemma ordinary_reconnect_split_nth_spec :
  forall l sub r h i s s',
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (ordinary_reconnect_split l sub r h) i = Some s' ->
    orn_seg s' = orn_seg s
    /\ init s' = operate_point l sub r h (init s)
    /\ term s' = operate_point l sub r h (term s).
Proof.
  intros l sub r h i s s' Hne Hconn Hmono Hsparse Hwhole Hembedded
    Hrec Hold Hnew.
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

(* 固定した sub との接続点を含め、再接続後も全体が同じ向き列を埋め込む。 *)
Lemma ordinary_reconnect_split_preserves_embed :
  forall l sub r h ds,
    sub <> [] ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    embed_listDir ds (ordinary_reconnect_split l sub r h).
Proof.
  intros l sub r h ds Hne Hmono Hsparse Hrec Hembed.
  assert (Hconn : connected sub).
  { apply connected_middle with (l := l) (r := r).
    now apply embed_listDir_connected with (ds := ds). }
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  eapply embed_scurve_transfer; [exact Hembed | | |].
  - unfold ordinary_reconnect_split. repeat rewrite length_app.
    rewrite !reconnect_segs_length. reflexivity.
  - intros i s s' Hold Hnew.
    exact (proj1 (ordinary_reconnect_split_nth_spec
                    l sub r h i s s' Hne Hconn Hmono Hsparse Hwhole
                    (ex_intro _ ds Hembed) Hrec Hold Hnew)).
  - intros i s1 s2 H1 H2.
    assert (Hlen :
        length (ordinary_reconnect_split l sub r h) = length (l ++ sub ++ r)).
    { unfold ordinary_reconnect_split. repeat rewrite length_app.
      rewrite !reconnect_segs_length. reflexivity. }
    assert (Hi : (i < length (l ++ sub ++ r))%nat).
    { rewrite <- Hlen. now apply nth_error_lt in H1. }
    assert (HSi : (S i < length (l ++ sub ++ r))%nat).
    { rewrite <- Hlen. now apply nth_error_lt in H2. }
    destruct (nth_error (l ++ sub ++ r) i) as [old1 |] eqn:E1.
    2: exfalso; apply (proj2 (nth_error_Some _ _) Hi); exact E1.
    destruct (nth_error (l ++ sub ++ r) (S i)) as [old2 |] eqn:E2.
    2: exfalso; apply (proj2 (nth_error_Some _ _) HSi); exact E2.
    pose proof (ordinary_reconnect_split_nth_spec
                  l sub r h i old1 s1 Hne Hconn Hmono Hsparse Hwhole
                  (ex_intro _ ds Hembed) Hrec E1 H1)
      as [_ [_ Hterm]].
    pose proof (ordinary_reconnect_split_nth_spec
                  l sub r h (S i) old2 s2 Hne Hconn Hmono Hsparse Hwhole
                  (ex_intro _ ds Hembed) Hrec E2 H2)
      as [_ [Hinit _]].
    rewrite Hterm, Hinit.
    f_equal. exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed
                      i old1 old2 E1 E2).
Qed.

Lemma ordinary_reconnect_split_length : forall l sub r h,
  length (ordinary_reconnect_split l sub r h) = length (l ++ sub ++ r).
Proof.
  intros. unfold ordinary_reconnect_split. repeat rewrite length_app.
  rewrite !reconnect_segs_length. reflexivity.
Qed.

(* 同じ旧セグメントに対応する通常版と安全版は、曲線の選び方が違っても
   二端点と向きが一致する。蓋の blocker を安全版へ輸送する基本補題。 *)
Lemma ordinary_safe_nth_same_box :
  forall l sub r h i old ordinary safe,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    nth_error (l ++ sub ++ r) i = Some old ->
    nth_error (ordinary_reconnect_split l sub r h) i = Some ordinary ->
    nth_error (reconnect_split l sub r h) i = Some safe ->
    same_segment_box ordinary safe /\ orn_seg ordinary = orn_seg safe.
Proof.
  intros l sub r h i old ordinary safe Hne Hconn Hmono Hh Hsparse Hwhole
    Hembedded Hext Hrec Hold Hordinary Hsafe.
  pose proof (ordinary_reconnect_split_nth_spec
                l sub r h i old ordinary Hne Hconn Hmono Hsparse Hwhole
                Hembedded Hrec Hold Hordinary) as HordinarySpec.
  pose proof (reconnect_split_reconnects_after
                l sub r h Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext
                Hrec) as HsafeRel.
  pose proof (Forall2_nth_error_relation
                Segment Segment (reconnects_after l sub r h)
                (l ++ sub ++ r) (reconnect_split l sub r h)
                HsafeRel i) as HsafeSpec.
  rewrite Hold, Hsafe in HsafeSpec.
  unfold reconnects_after in HsafeSpec.
  destruct HordinarySpec as [HordinaryOrn [HordinaryInit HordinaryTerm]].
  destruct HsafeSpec as [HsafeInit [HsafeTerm HsafeOrn]].
  split.
  - unfold same_segment_box. split.
    + rewrite HordinaryInit, HsafeInit. reflexivity.
    + rewrite HordinaryTerm, HsafeTerm. reflexivity.
  - rewrite HordinaryOrn, HsafeOrn. reflexivity.
Qed.

Lemma nth_error_zero_hd_segment : forall ls,
  ls <> [] -> nth_error ls 0 = Some (hd_segment ls).
Proof.
  intros [|s ls] Hne; [contradiction | reflexivity].
Qed.

Lemma ordinary_safe_head_same_box :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    same_segment_box
      (hd_segment (ordinary_reconnect_split l sub r h))
      (hd_segment (reconnect_split l sub r h)).
Proof.
  intros l sub r h Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hrec.
  assert (HoldNe : l ++ sub ++ r <> []).
  { intros Hnil. apply app_eq_nil in Hnil as [_ Htail].
    apply app_eq_nil in Htail as [Hsub _]. contradiction. }
  assert (HordinaryNe : ordinary_reconnect_split l sub r h <> []).
  { intros Hnil. apply HoldNe, length_zero_iff_nil.
    rewrite <- (ordinary_reconnect_split_length l sub r h). now rewrite Hnil. }
  assert (HsafeNe : reconnect_split l sub r h <> []).
  { intros Hnil. apply HoldNe, length_zero_iff_nil.
    rewrite <- (reconnect_split_safe_length l sub r h). now rewrite Hnil. }
  pose proof (ordinary_safe_nth_same_box
                l sub r h 0
                (hd_segment (l ++ sub ++ r))
                (hd_segment (ordinary_reconnect_split l sub r h))
                (hd_segment (reconnect_split l sub r h))
                Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hrec
                (nth_error_zero_hd_segment _ HoldNe)
                (nth_error_zero_hd_segment _ HordinaryNe)
                (nth_error_zero_hd_segment _ HsafeNe)) as [Hbox _].
  exact Hbox.
Qed.

Lemma ordinary_safe_last_same_box :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    same_segment_box
      (last_segment (ordinary_reconnect_split l sub r h))
      (last_segment (reconnect_split l sub r h)).
Proof.
  intros l sub r h Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hrec.
  set (old := l ++ sub ++ r).
  set (ordinary := ordinary_reconnect_split l sub r h).
  set (safe := reconnect_split l sub r h).
  assert (HoldNe : old <> []).
  { unfold old. intros Hnil. apply app_eq_nil in Hnil as [_ Htail].
    apply app_eq_nil in Htail as [Hsub _]. contradiction. }
  assert (HordinaryLen : length ordinary = length old).
  { unfold ordinary, old. apply ordinary_reconnect_split_length. }
  assert (HsafeLen : length safe = length old).
  { unfold safe, old. apply reconnect_split_safe_length. }
  assert (HordinaryNe : ordinary <> []).
  { intros Hnil. apply HoldNe, length_zero_iff_nil.
    rewrite <- HordinaryLen. now rewrite Hnil. }
  assert (HsafeNe : safe <> []).
  { intros Hnil. apply HoldNe, length_zero_iff_nil.
    rewrite <- HsafeLen. now rewrite Hnil. }
  assert (HoldNth :
      nth_error old (length old - 1) = Some (last_segment old)).
  { exact (@nth_error_last Segment old default_segment HoldNe). }
  assert (HordinaryNth :
      nth_error ordinary (length old - 1) = Some (last_segment ordinary)).
  { rewrite <- HordinaryLen.
    exact (@nth_error_last Segment ordinary default_segment HordinaryNe). }
  assert (HsafeNth :
      nth_error safe (length old - 1) = Some (last_segment safe)).
  { rewrite <- HsafeLen.
    exact (@nth_error_last Segment safe default_segment HsafeNe). }
  unfold old, ordinary, safe in *.
  pose proof (ordinary_safe_nth_same_box
                l sub r h (length (l ++ sub ++ r) - 1)
                (last_segment (l ++ sub ++ r))
                (last_segment (ordinary_reconnect_split l sub r h))
                (last_segment (reconnect_split l sub r h))
                Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hrec
                HoldNth HordinaryNth HsafeNth) as [Hbox _].
  exact Hbox.
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

Lemma safe_head_strict_extension_iff_ordinary :
  forall ds l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    onHead_extend_strict (reconnect_split l sub r h) p <->
    onHead_extend_strict (ordinary_reconnect_split l sub r h) p.
Proof.
  intros ds l sub r h p Hne Hconn Hmono Hh Hsparse Hembed Hext.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { now apply (embed_listDir_connected ds (l ++ sub ++ r)). }
  pose proof (operate_endpoints_reconnectable
                l sub r h Hne Hconn Hmono Hh Hsparse Hwhole
                (ex_intro _ ds Hembed) Hext) as Hrec.
  pose proof (ordinary_safe_head_same_box
                l sub r h Hne Hconn Hmono Hh Hsparse Hwhole
                (ex_intro _ ds Hembed) Hext Hrec) as Hbox.
  unfold onHead_extend_strict.
  eapply strict_head_extension_same.
  - symmetry. exact (proj1 Hbox).
  - intros q. exact (safe_head_extension_iff_ordinary
                       ds l sub r h q Hne Hconn Hmono Hh Hsparse Hembed Hext).
Qed.

Lemma safe_last_strict_extension_iff_ordinary :
  forall ds l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    onLast_extend_strict (reconnect_split l sub r h) p <->
    onLast_extend_strict (ordinary_reconnect_split l sub r h) p.
Proof.
  intros ds l sub r h p Hne Hconn Hmono Hh Hsparse Hembed Hext.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { now apply (embed_listDir_connected ds (l ++ sub ++ r)). }
  pose proof (operate_endpoints_reconnectable
                l sub r h Hne Hconn Hmono Hh Hsparse Hwhole
                (ex_intro _ ds Hembed) Hext) as Hrec.
  pose proof (ordinary_safe_last_same_box
                l sub r h Hne Hconn Hmono Hh Hsparse Hwhole
                (ex_intro _ ds Hembed) Hext Hrec) as Hbox.
  unfold onLast_extend_strict.
  eapply strict_last_extension_same.
  - symmetry. exact (proj2 Hbox).
  - intros q. exact (safe_last_extension_iff_ordinary
                       ds l sub r h q Hne Hconn Hmono Hh Hsparse Hembed Hext).
Qed.
