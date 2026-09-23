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


(* 分類器に要求する外部仕様。 *)
Record ClassificationSpec
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

  (* x 範囲が重なる非隣接セグメントの端点順序を保存する。
     固定する sub 上の target はこの順序制約の対象にしない。 *)
  classified_nonadjacent_endpoint_order :
    forall i j s t ps pt,
      nth_error (l ++ sub ++ r) i = Some s ->
      nth_error (l ++ sub ++ r) j = Some t ->
      (S i < j \/ S j < i)%nat ->
      segment_x_ranges_overlap s t ->
      endpoint_of_seg s ps ->
      endpoint_of_seg t pt ->
      ~ onSegmentlist sub pt ->
      snd ps <= snd pt ->
      region_at_or_above (classifier pt) (classifier ps);

  (* l 末尾の端点長方形より完全に下にある端点は、固定接続点へ
     向かって上昇させない。隣接端点も含めて要求する。 *)
  classified_below_terminal_not_up :
    l <> [] ->
    forall p,
      endpoint_of (l ++ sub ++ r) p ->
      snd p < ry0 (rect_of [last_segment l]) ->
      classifier p <> RegUp;

  (* r 先頭についても、その長方形より完全に下にある全端点を
     上昇させない。 *)
  classified_below_initial_not_up :
    r <> [] ->
    forall p,
      endpoint_of (l ++ sub ++ r) p ->
      snd p < ry0 (rect_of [hd_segment r]) ->
      classifier p <> RegUp;

  (* sub の x 範囲でその上側・下側を通る非隣接セグメントは、
     両端を同じ外側へ動かす。 *)
  classified_segment_at_sub_x :
    forall seg p,
      In seg (nonadjacent_sides l r) ->
      onSegment seg p ->
      in_sub_x_range sub p ->
      (above_sub_at_x sub p ->
         classifier (init seg) = RegUp
         /\ classifier (term seg) = RegUp)
      /\
      (below_sub_at_x sub p ->
         classifier (init seg) = RegDown
         /\ classifier (term seg) = RegDown);

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
      \/ classifier (term (last_segment (l ++ sub ++ r))) = RegDown;

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
           (classifier (term seg)));

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
