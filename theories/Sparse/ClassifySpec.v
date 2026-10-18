Require Export Sparse.ClassifyDefinition.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* 分類を構成するための幾何学的文脈。 *)
Record ClassificationContext
    (l sub r : list Segment) : Prop := {
  context_sub_nonempty : sub <> [];
  context_sub_x_monotone : x_monotone_segs sub;
  context_sparse : sparse_embedding (l ++ sub ++ r);
  context_whole_embedded :
    exists ds, embed_listDir ds (l ++ sub ++ r);
  context_extensions_disjoint : extensions_disjoint (l ++ sub ++ r)
}.


(* 端点移動・先頭末尾の傾き・延長線二本の順序に共通する仕様。 *)
Record EndpointMovementSpec
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

(* PMP 用の従来の順序仕様。PPMM・PM は sub との順序を別に扱う。 *)
Record ReconnectClassificationSpec
    (l sub r : list Segment) {classifier : EndpointClassifier} : Prop := {
  reconnect_endpoint_spec :> @EndpointMovementSpec l sub r classifier;

  (* 非隣接の閉三角形が同じ x で上下に並ぶとき、その全端点の
     移動方向も同じ順序にする。再接続後の三角形分離に用いる。 *)
  classified_nonadjacent_triangle_order :
    forall i j s t ps pt u v,
      nth_error (l ++ sub ++ r) i = Some s ->
      nth_error (l ++ sub ++ r) j = Some t ->
      (S i < j \/ S j < i)%nat ->
      endpoint_of_seg s ps ->
      endpoint_of_seg t pt ->
      in_segment_triangle s u ->
      in_segment_triangle t v ->
      fst u = fst v ->
      snd u < snd v ->
      region_at_or_above (classifier pt) (classifier ps);

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
           (classifier (term seg)))
}.

(* PPMM・PM 用：外側の順序を保存し、sub 長方形からは上下へ退避する。 *)
Record ClassificationSpec
    (l sub r : list Segment) {classifier : EndpointClassifier} : Prop := {
  classification_endpoint_spec :> @EndpointMovementSpec l sub r classifier;

  (* 外側の非隣接閉三角形が同じ x で上下に並ぶとき、その全端点の
     移動方向も同じ順序にする。再接続後の三角形分離に用いる。 *)
  classified_external_triangle_order :
    forall i j s t ps pt u v,
      nth_error (l ++ sub ++ r) i = Some s ->
      nth_error (l ++ sub ++ r) j = Some t ->
      (S i < j \/ S j < i)%nat ->
      In s (l ++ r) -> In t (l ++ r) ->
      endpoint_of_seg s ps ->
      endpoint_of_seg t pt ->
      in_segment_triangle s u ->
      in_segment_triangle t v ->
      fst u = fst v ->
      snd u < snd v ->
      region_at_or_above (classifier pt) (classifier ps);

  (* 外側とは常に比較する。sub との比較だけ、当該延長線点が gap 内なら外す。 *)
  classified_head_segment_crossing_order_outside_gap :
    forall seg e q,
      (In seg (l ++ r) \/
       (In seg sub /\ avoids_sub_vertical_gap sub q)) ->
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

  (* 末尾も同様。独立した全体所属条件は、この二分岐に吸収している。 *)
  classified_last_segment_crossing_order_outside_gap :
    forall seg e q,
      (In seg (l ++ r) \/
       (In seg sub /\ avoids_sub_vertical_gap sub q)) ->
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

  (* sub の閉 x 範囲を通る非隣接セグメントは、両端を同じ非固定領域にする。 *)
  classified_segment_at_sub_x :
    forall seg p,
      In seg (nonadjacent_sides l r) ->
      onSegment seg p ->
      in_sub_x_range sub p ->
      (classifier (init seg) = RegUp /\ classifier (term seg) = RegUp)
      \/ (classifier (init seg) = RegDown /\ classifier (term seg) = RegDown);

  (* x 範囲内の端点が sub 長方形の上辺を越えるなら上へ動かす。 *)
  classified_endpoint_above_sub_rect :
    forall seg p,
      In seg (nonadjacent_sides l r) ->
      endpoint_of_seg seg p ->
      in_sub_x_range sub p ->
      ry1 (rect_of sub) < snd p ->
      classifier p = RegUp;

  (* 下辺より下の端点については下へ動かす。x 範囲外には要求しない。 *)
  classified_endpoint_below_sub_rect :
    forall seg p,
      In seg (nonadjacent_sides l r) ->
      endpoint_of_seg seg p ->
      in_sub_x_range sub p ->
      snd p < ry0 (rect_of sub) ->
      classifier p = RegDown;

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
      \/ classifier (term (last_segment (l ++ sub ++ r))) = RegDown
}.

(* PMP 用：下方向へは動かさず、Plus 側の三角形だけから退避する。 *)
Record PMPClassificationSpec
    (l sub r : list Segment) {classifier : EndpointClassifier} : Prop := {
  pmp_reconnect_spec :> @ReconnectClassificationSpec l sub r classifier;
  (* 分類は上移動または固定の二択。 *)
  pmp_only_up_or_fix : forall p, classifier p = RegUp \/ classifier p = RegFix;
  (* sub の x 範囲を通る非隣接セグメントは一律に動かす。 *)
  pmp_segment_at_sub_x_uniform : forall seg p,
    In seg (nonadjacent_sides l r) -> onSegment seg p ->
    in_sub_x_range sub p -> classifier (init seg) = classifier (term seg);
  (* 退避方向は入力側の Plus 三角形との接触から決める。 *)
  pmp_triangle_meeting_moves_up : forall seg p,
    In seg (nonadjacent_sides l r) ->
    in_segment_triangle seg p -> in_sub_triangle Plus sub p ->
    classifier (init seg) = RegUp /\ classifier (term seg) = RegUp;
  (* 外側の延長線が目的三角形に入るとき、その基点を上げる。 *)
  pmp_head_meeting_moves_up : l <> [] -> forall p,
    onHead_extend_strict (l ++ sub ++ r) p -> in_sub_triangle Plus sub p ->
    classifier (init (hd_segment (l ++ sub ++ r))) = RegUp;
  pmp_last_meeting_moves_up : r <> [] -> forall p,
    onLast_extend_strict (l ++ sub ++ r) p -> in_sub_triangle Plus sub p ->
    classifier (term (last_segment (l ++ sub ++ r))) = RegUp
}.
