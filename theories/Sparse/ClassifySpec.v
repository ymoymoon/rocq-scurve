Require Export Sparse.ClassifyDefinition.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Relations.Relation_Operators.

Record ClassificationSpec (l sub r : list Segment) : Prop := {

  (* sub は固定 *)
  classified_sub_fixed :
    forall p, onSegmentlist sub p -> classify l sub r p = RegFix;

  (* セグメントの始点が終点より低く，始点の領域が Up なら終点も Up など *)
  classified_segment_endpoints_monotone :
    forall s,
      In s (l ++ sub ++ r) ->
      (snd (init s) < snd (term s) ->
        region_at_or_above (classify l sub r (term s)) (classify l sub r (init s)))
      /\
      (snd (term s) < snd (init s) ->
        region_at_or_above (classify l sub r (init s)) (classify l sub r (term s)));

  (* x 範囲が重なる非隣接セグメントについては、sub 上にある端点を
     除き、下側の長方形が Up なら上側の長方形も Up など。 *)
  classified_nonadjacent_endpoint_order :
    forall i j s t ps pt,
      nth_error (l ++ sub ++ r) i = Some s ->
      nth_error (l ++ sub ++ r) j = Some t ->
      (S i < j \/ S j < i)%nat ->
      segment_x_ranges_overlap s t ->
      endpoint_of_seg s ps ->
      endpoint_of_seg t pt ->
      ~ onSegmentlist sub ps ->
      ~ onSegmentlist sub pt ->
      snd ps <= snd pt ->
      region_at_or_above
        (classify l sub r pt) (classify l sub r ps);

  (* sub と同じ x 座標を持つセグメントは Up もしくは Down *)
  classified_segment_at_sub_x :
    forall s p,
      In s (nonadjacent_sides l r) ->
      onSegment s p ->
      in_sub_x_range sub p ->
      (above_sub_at_x sub p ->
         classify l sub r (init s) = RegUp
         /\ classify l sub r (term s) = RegUp)
      /\
      (below_sub_at_x sub p ->
         classify l sub r (init s) = RegDown
         /\ classify l sub r (term s) = RegDown);

  (* strict 延長線が sub 長方形の閉 x 範囲へ入る場合，
     その延長線を動かす基点は Fix ではない。 *)
  classified_head_extension_at_sub_x :
    forall p,
      onHead_extend_strict (l ++ sub ++ r) p ->
      rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub) ->
      classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegUp
      \/ classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegDown;

  classified_last_extension_at_sub_x :
    forall p,
      onLast_extend_strict (l ++ sub ++ r) p ->
      rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub) ->
      classify l sub r (term (last_segment (l ++ sub ++ r))) = RegUp
      \/ classify l sub r (term (last_segment (l ++ sub ++ r))) = RegDown;

  (* 延長線が同じ x 座標の点を持つ時，下側が Up なら上側も Up など *)
  classified_head_last_extension_order :
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
           (classify l sub r (term (last_segment (l ++ sub ++ r)))));

  (* セグメントと延長線が同じ x 座標の点を持つ時，下側が Up なら上側も Up など *)
  classified_head_segment_crossing_order :
    forall s e q,
      In s (l ++ sub ++ r) ->
      onSegment s e ->
      onHead_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      (snd q < snd e ->
         region_at_or_above
           (classify l sub r (init s))
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
         /\ region_at_or_above
           (classify l sub r (term s))
           (classify l sub r (init (hd_segment (l ++ sub ++ r)))))
      /\
      (snd e < snd q ->
         region_at_or_above
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
           (classify l sub r (init s))
         /\ region_at_or_above
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
           (classify l sub r (term s)));

  classified_last_segment_crossing_order :
    forall s e q,
      In s (l ++ sub ++ r) ->
      onSegment s e ->
      onLast_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      (snd q < snd e ->
         region_at_or_above
           (classify l sub r (init s))
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
         /\ region_at_or_above
           (classify l sub r (term s))
           (classify l sub r (term (last_segment (l ++ sub ++ r)))))
      /\
      (snd e < snd q ->
         region_at_or_above
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
           (classify l sub r (init s))
         /\ region_at_or_above
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
           (classify l sub r (term s)));

  (* 先頭の両端が別領域なら、始点傾きを保てる向き・凸性に限る。 *)
  classified_head_slope_case :
    l <> [] ->
    classify l sub r (init (hd_segment l)) =
      classify l sub r (term (hd_segment l))
    \/ (classify l sub r (init (hd_segment l)) = RegUp
        /\ (embed (s, w, cx) (hd_segment l)
            \/ embed (s, e, cx) (hd_segment l)))
    \/ (classify l sub r (init (hd_segment l)) = RegDown
        /\ (embed (n, w, cc) (hd_segment l)
            \/ embed (n, e, cc) (hd_segment l)));

  (* 末尾では双対的に、終点傾きを保てる場合だけ別領域を許す。 *)
  classified_last_slope_case :
    r <> [] ->
    classify l sub r (init (last_segment r)) =
      classify l sub r (term (last_segment r))
    \/ (classify l sub r (term (last_segment r)) = RegUp
        /\ (embed (n, w, cx) (last_segment r)
            \/ embed (n, e, cx) (last_segment r)))
    \/ (classify l sub r (term (last_segment r)) = RegDown
        /\ (embed (s, w, cc) (last_segment r)
            \/ embed (s, e, cc) (last_segment r)))
}.
