Require Export Sparse.ClassifySpec.
Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Reals.Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
Open Scope R_scope.

Lemma classify_at_height_vertical_order :
  forall height p q,
    fst p = fst q ->
    snd p < snd q ->
    region_at_or_above
      (classify_at_height height q)
      (classify_at_height height p).
Proof.
  intros height [xp yp] [xq yq] Hx Hy. simpl in Hx, Hy. subst xq.
  unfold classify_at_height. simpl.
  destruct (Rlt_dec yp (height xp)) as [Hpdown | Hpdown].
  - destruct (Rlt_dec yq (height xp)) as [Hqdown | Hqdown].
    + now left.
    + destruct (Rlt_dec (height xp) yq) as [Hqup | Hqup].
      * right. apply RegUp_above_Down.
      * right. apply RegFix_above_Down.
  - destruct (Rlt_dec (height xp) yp) as [Hpup | Hpup].
    + destruct (Rlt_dec yq (height xp)) as [Hqdown | Hqdown]; [lra |].
      destruct (Rlt_dec (height xp) yq) as [Hqup | Hqup]; [now left | lra].
    + destruct (Rlt_dec yq (height xp)) as [Hqdown | Hqdown]; [lra |].
      destruct (Rlt_dec (height xp) yq) as [Hqup | Hqup].
      * right. apply RegUp_above_Fix.
      * lra.
Qed.

Lemma simple_classify_vertical_order :
  forall sub p q,
    fst p = fst q ->
    snd p < snd q ->
    region_at_or_above
      (state_region (simple_classify_state sub) q)
      (state_region (simple_classify_state sub) p).
Proof.
  intros sub p q Hx Hy.
  exact (classify_at_height_vertical_order
           (simple_height sub) p q Hx Hy).
Qed.

Definition vertically_monotone_region (f : Point -> Region) : Prop :=
  forall p q,
    fst p = fst q ->
    snd p < snd q ->
    region_at_or_above (f q) (f p).

Lemma apply_region_patch_preserves_vertical_monotonicity :
  forall old patch,
    vertically_monotone_region old ->
    vertically_monotone_region (apply_region_patch old patch).
Proof.
  intros old [side start trace force inclusive] Hold
    [xp yp] [xq yq] Hx Hy.
  simpl in Hx, Hy. subst xq.
  unfold apply_region_patch. simpl.
  destruct (patch_active_dec
              {| patch_side := side;
                 patch_start_x := start;
                 patch_reference := trace;
                 patch_force := force;
                 patch_inclusive := inclusive |} xp) as [Hactive | Hinactive].
  2: apply Hold; simpl; lra.
  destruct (trace_height trace xp) as [reference_y |] eqn:Hheight.
  2: apply Hold; simpl; lra.
  destruct force, inclusive;
    cbn [patch_forces_dec patch_forces_at forced_region].
  - destruct (Rle_dec reference_y yp) as [Hp | Hp];
    destruct (Rle_dec reference_y yq) as [Hq | Hq]; simpl.
    + now left.
    + lra.
    + destruct (old (xp, yp));
        [right; apply RegUp_above_Fix | now left | right; apply RegUp_above_Down].
    + apply Hold; simpl; lra.
  - destruct (Rlt_dec reference_y yp) as [Hp | Hp];
    destruct (Rlt_dec reference_y yq) as [Hq | Hq]; simpl.
    + now left.
    + lra.
    + destruct (old (xp, yp));
        [right; apply RegUp_above_Fix | now left | right; apply RegUp_above_Down].
    + apply Hold; simpl; lra.
  - destruct (Rle_dec yp reference_y) as [Hp | Hp];
    destruct (Rle_dec yq reference_y) as [Hq | Hq]; simpl.
    + now left.
    + destruct (old (xp, yq));
        [right; apply RegFix_above_Down | right; apply RegUp_above_Down | now left].
    + lra.
    + apply Hold; simpl; lra.
  - destruct (Rlt_dec yp reference_y) as [Hp | Hp];
    destruct (Rlt_dec yq reference_y) as [Hq | Hq]; simpl.
    + now left.
    + destruct (old (xp, yq));
        [right; apply RegFix_above_Down | right; apply RegUp_above_Down | now left].
    + lra.
    + apply Hold; simpl; lra.
Qed.

Lemma apply_patch_preserves_vertical_monotonicity :
  forall st patch,
    vertically_monotone_region (state_region st) ->
    vertically_monotone_region (state_region (apply_patch st patch)).
Proof.
  intros [region height] patch Hmono. simpl in *.
  now apply apply_region_patch_preserves_vertical_monotonicity.
Qed.

Lemma simple_state_vertically_monotone :
  forall sub,
    vertically_monotone_region (state_region (simple_classify_state sub)).
Proof.
  intros sub p q Hx Hy.
  now apply simple_classify_vertical_order.
Qed.

Lemma apply_end_at_preserves_vertical_monotonicity :
  forall st l r k side,
    vertically_monotone_region (state_region st) ->
    vertically_monotone_region
      (state_region (apply_end_at st l r k side)).
Proof.
  intros st l r k side Hmono. unfold apply_end_at.
  destruct (make_end_patch l r k side) as [patch |];
    [now apply apply_patch_preserves_vertical_monotonicity | exact Hmono].
Qed.

Lemma process_end_preserves_vertical_monotonicity :
  forall st l sub r k side,
    vertically_monotone_region (state_region st) ->
    vertically_monotone_region
      (state_region (process_end st l sub r k side)).
Proof.
  intros st l sub r k side Hmono. unfold process_end.
  destruct (nearest_end_crossing st l sub r k side);
    [now apply apply_end_at_preserves_vertical_monotonicity | exact Hmono].
Qed.

Lemma process_both_ends_preserves_vertical_monotonicity :
  forall st l sub r side,
    vertically_monotone_region (state_region st) ->
    vertically_monotone_region
      (state_region (process_both_ends_on_side st l sub r side)).
Proof.
  intros st l sub r side Hmono.
  unfold process_both_ends_on_side.
  destruct (nearest_end_crossing st l sub r HeadEnd side) as [ph |];
  destruct (nearest_end_crossing st l sub r LastEnd side) as [pl |].
  - destruct (crossing_closer_dec side ph pl).
    + apply process_end_preserves_vertical_monotonicity.
      now apply apply_end_at_preserves_vertical_monotonicity.
    + apply process_end_preserves_vertical_monotonicity.
      now apply apply_end_at_preserves_vertical_monotonicity.
  - now apply apply_end_at_preserves_vertical_monotonicity.
  - now apply apply_end_at_preserves_vertical_monotonicity.
  - exact Hmono.
Qed.

Lemma build_classify_state_vertically_monotone :
  forall l sub r,
    vertically_monotone_region
      (state_region (build_classify_state l sub r)).
Proof.
  intros l sub r. unfold build_classify_state.
  apply process_both_ends_preserves_vertical_monotonicity.
  apply process_both_ends_preserves_vertical_monotonicity.
  apply simple_state_vertically_monotone.
Qed.

Lemma classify_vertical_order :
  forall l sub r p q,
    fst p = fst q ->
    snd p < snd q ->
    region_at_or_above
      (classify l sub r q) (classify l sub r p).
Proof.
  intros l sub r p q Hx Hy.
  exact (build_classify_state_vertically_monotone l sub r p q Hx Hy).
Qed.

(* 補正後の Fix は元の単純分類でも Fix なので、同じ x の Fix 点より
   真に上（下）の非 Fix 点は最終分類でも Up（Down）になる。 *)
Lemma classify_above_fixed_is_up :
  forall l sub r p q,
    fst p = fst q ->
    snd q < snd p ->
    classify l sub r q = RegFix ->
    state_region (simple_classify_state sub) p <> RegFix ->
    classify l sub r p = RegUp.
Proof.
  intros l sub r p q Hx Hy Hq Hsimple.
  pose proof (classify_vertical_order l sub r q p
                ltac:(now symmetry) Hy) as Horder.
  rewrite Hq in Horder.
  destruct (classify l sub r p) eqn:Hp.
  - exfalso. apply Hsimple.
    now apply (classify_fix_implies_simple_fix l sub r p).
  - reflexivity.
  - destruct Horder as [Heq | Habove]; [discriminate | inversion Habove].
Qed.

Lemma classify_below_fixed_is_down :
  forall l sub r p q,
    fst p = fst q ->
    snd p < snd q ->
    classify l sub r q = RegFix ->
    state_region (simple_classify_state sub) p <> RegFix ->
    classify l sub r p = RegDown.
Proof.
  intros l sub r p q Hx Hy Hq Hsimple.
  pose proof (classify_vertical_order l sub r p q Hx Hy) as Horder.
  rewrite Hq in Horder.
  destruct (classify l sub r p) eqn:Hp.
  - exfalso. apply Hsimple.
    now apply (classify_fix_implies_simple_fix l sub r p).
  - destruct Horder as [Heq | Habove]; [discriminate | inversion Habove].
  - reflexivity.
Qed.

(* sub 固定性は、prepared な patch 構成の局所安全性から導く。 *)
Lemma classified_sub_fixed_from_construction :
  forall l sub r,
    PreparedGeometry l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall p, onSegmentlist sub p -> classify l sub r p = RegFix.
Proof.
  intros l sub r Hgeometry Hsparse Hwhole p Hp.
  admit.
Admitted.

(* sub と同じ x の点の上下分類は、prepared な sub の局所幾何から導く。 *)
Lemma classify_above_sub_at_x :
  forall l sub r p,
    PreparedGeometry l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    above_sub_at_x sub p ->
    classify l sub r p = RegUp.
Proof.
  intros. admit.
Admitted.

Lemma classify_below_sub_at_x :
  forall l sub r p,
    PreparedGeometry l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    below_sub_at_x sub p ->
    classify l sub r p = RegDown.
Proof.
  intros. admit.
Admitted.

(* 各セグメントと現在の境界の交差順序。primitive の8場合に帰着するが、
   更新済み境界を横切る場合の中間値議論を残す。 *)
Lemma classified_segment_endpoints_monotone_from_construction :
  forall l sub r,
    PreparedGeometry l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall seg,
      In seg (l ++ sub ++ r) ->
      (snd (init seg) < snd (term seg) ->
        region_at_or_above
          (classify l sub r (term seg)) (classify l sub r (init seg)))
      /\
      (snd (term seg) < snd (init seg) ->
        region_at_or_above
          (classify l sub r (init seg)) (classify l sub r (term seg))).
Admitted.

(* sub の同じ x に点を持つ非隣接セグメントについて、疎性から長方形の
   上下どちら側に全端点があるかを確定する部分。 *)
Lemma classified_segment_at_sub_x_from_construction :
  forall l sub r,
    PreparedGeometry l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall seg p,
      In seg (nonadjacent_sides l r) ->
      onSegment seg p ->
      in_sub_x_range sub p ->
      (above_sub_at_x sub p ->
         classify l sub r (init seg) = RegUp
         /\ classify l sub r (term seg) = RegUp)
      /\
      (below_sub_at_x sub p ->
         classify l sub r (init seg) = RegDown
         /\ classify l sub r (term seg) = RegDown).
Admitted.

(* strict 延長線が sub の x 範囲へ入る場合の先頭基点分類。 *)
Lemma classified_head_extension_at_sub_x_from_construction :
  forall l sub r,
    PreparedGeometry l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall p,
      onHead_extend_strict (l ++ sub ++ r) p ->
      rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub) ->
      classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegUp
      \/ classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegDown.
Admitted.

(* 上の末尾側の双対。 *)
Lemma classified_last_extension_at_sub_x_from_construction :
  forall l sub r,
    PreparedGeometry l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall p,
      onLast_extend_strict (l ++ sub ++ r) p ->
      rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub) ->
      classify l sub r (term (last_segment (l ++ sub ++ r))) = RegUp
      \/ classify l sub r (term (last_segment (l ++ sub ++ r))) = RegDown.
Admitted.

(* 同じ x にある先頭・末尾延長線の上下順序。 *)
Lemma classified_head_last_extension_order_from_construction :
  forall l sub r,
    PreparedGeometry l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall ph pl,
      onHead_extend (l ++ sub ++ r) ph ->
      onLast_extend (l ++ sub ++ r) pl ->
      fst ph = fst pl ->
      (snd ph < snd pl ->
         region_at_or_above
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
           (classify l sub r (init (hd_segment (l ++ sub ++ r)))))
      /\
      (snd pl < snd ph ->
         region_at_or_above
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
           (classify l sub r (term (last_segment (l ++ sub ++ r))))).
Admitted.

(* 先頭延長線と一セグメントの交差順序。 *)
Lemma classified_head_segment_crossing_order_from_construction :
  forall l sub r,
    PreparedGeometry l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall seg e0 q,
      In seg (l ++ sub ++ r) ->
      onSegment seg e0 ->
      onHead_extend_strict (l ++ sub ++ r) q ->
      fst e0 = fst q ->
      (snd q < snd e0 ->
         region_at_or_above
           (classify l sub r (init seg))
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
         /\ region_at_or_above
           (classify l sub r (term seg))
           (classify l sub r (init (hd_segment (l ++ sub ++ r)))))
      /\
      (snd e0 < snd q ->
         region_at_or_above
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
           (classify l sub r (init seg))
         /\ region_at_or_above
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
           (classify l sub r (term seg))).
Admitted.

(* 上の末尾側の双対。 *)
Lemma classified_last_segment_crossing_order_from_construction :
  forall l sub r,
    PreparedGeometry l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall seg e0 q,
      In seg (l ++ sub ++ r) ->
      onSegment seg e0 ->
      onLast_extend_strict (l ++ sub ++ r) q ->
      fst e0 = fst q ->
      (snd q < snd e0 ->
         region_at_or_above
           (classify l sub r (init seg))
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
         /\ region_at_or_above
           (classify l sub r (term seg))
           (classify l sub r (term (last_segment (l ++ sub ++ r)))))
      /\
      (snd e0 < snd q ->
         region_at_or_above
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
           (classify l sub r (init seg))
         /\ region_at_or_above
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
           (classify l sub r (term seg))).
Admitted.

(* 先頭補正表の8 primitive 場合から、異領域となる場合を傾き保存可能な
   四形に限定する部分。 *)
Lemma classified_head_slope_case_from_construction :
  forall l sub r,
    PreparedGeometry l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    l <> [] ->
    classify l sub r (init (hd_segment l)) =
      classify l sub r (term (hd_segment l))
    \/ (classify l sub r (init (hd_segment l)) = RegUp
        /\ (embed (s, w, cx) (hd_segment l)
            \/ embed (s, e, cx) (hd_segment l)))
    \/ (classify l sub r (init (hd_segment l)) = RegDown
        /\ (embed (n, w, cc) (hd_segment l)
            \/ embed (n, e, cc) (hd_segment l))).
Admitted.

(* 末尾補正表の双対。 *)
Lemma classified_last_slope_case_from_construction :
  forall l sub r,
    PreparedGeometry l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    r <> [] ->
    classify l sub r (init (last_segment r)) =
      classify l sub r (term (last_segment r))
    \/ (classify l sub r (term (last_segment r)) = RegUp
        /\ (embed (n, w, cx) (last_segment r)
            \/ embed (n, e, cx) (last_segment r)))
    \/ (classify l sub r (term (last_segment r)) = RegDown
        /\ (embed (s, w, cc) (last_segment r)
            \/ embed (s, e, cc) (last_segment r))).
Admitted.

(* 蓋でない左境界の完全下側にある非隣接端点は上へ動かさない。
   現行の境界パッチ構成に固有の幾何学的検証は、再接続側と分離しておく。 *)
Lemma classified_below_terminal_not_up_from_construction :
  forall l sub r,
    PreparedGeometry l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    l <> [] ->
    ~ terminal_backtrack_lid l ->
    forall t p,
      In t (nonadjacent_sides l r) ->
      segment_x_ranges_overlap t (last_segment l) ->
      ry1 (rect_of [t]) < ry0 (rect_of [last_segment l]) ->
      endpoint_of_seg t p ->
      classify l sub r p <> RegUp.
Admitted.

(* 右境界についての双対。 *)
Lemma classified_below_initial_not_up_from_construction :
  forall l sub r,
    PreparedGeometry l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    r <> [] ->
    ~ initial_backtrack_lid r ->
    forall t p,
      In t (nonadjacent_sides l r) ->
      segment_x_ranges_overlap t (hd_segment r) ->
      ry1 (rect_of [t]) < ry0 (rect_of [hd_segment r]) ->
      endpoint_of_seg t p ->
      classify l sub r p <> RegUp.
Admitted.

(* 蓋がない場合には、sub 上の端点を除外せずに非隣接長方形の順序を
   分類順序へ移せる。これは patch 構成の全域 sparse 用の検証部分である。 *)
Lemma classified_nonadjacent_endpoint_order_no_lid_from_construction :
  forall l sub r,
    PreparedGeometry l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    ~ terminal_lid l sub r ->
    ~ initial_lid l sub r ->
    forall i j s t ps pt,
      nth_error (l ++ sub ++ r) i = Some s ->
      nth_error (l ++ sub ++ r) j = Some t ->
      (S i < j \/ S j < i)%nat ->
      segment_x_ranges_overlap s t ->
      endpoint_of_seg s ps ->
      endpoint_of_seg t pt ->
      snd ps <= snd pt ->
      region_at_or_above
        (classify l sub r pt) (classify l sub r ps).
Admitted.

(* 先頭・末尾 patch の表は、許された例外も含めて指定側の傾きを
   保存して再接続できることを保証する。 *)
Lemma classified_head_init_slope_reconnectable_from_construction :
  forall l sub r h,
    PreparedGeometry l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    0 <= h ->
    l <> [] ->
    classified_init_slope_reconnectable (classify l sub r) h (hd_segment l).
Admitted.

Lemma classified_last_term_slope_reconnectable_from_construction :
  forall l sub r h,
    PreparedGeometry l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    0 <= h ->
    r <> [] ->
    classified_term_slope_reconnectable (classify l sub r) h (last_segment r).
Admitted.
