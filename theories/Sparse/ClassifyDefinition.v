Require Export Sparse.ClassifyGeometry.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Relations.Relation_Operators.

(* 端点間の順序、seed、およびそれらから定まる具体的分類器。 *)
Inductive endpoint_core_step
    (l sub r : list Segment) : Point -> Point -> Prop :=
  (* 同一セグメントでは、低い端点から高い端点へ領域順序を付ける。 *)
  | order_on_segment : forall seg p q,
      In seg (l ++ sub ++ r) ->
      endpoint_of_seg seg p ->
      endpoint_of_seg seg q ->
      snd p <= snd q ->
      endpoint_core_step l sub r p q
  (* x 範囲が重なる非隣接セグメント間では、低い端点から高い端点へ制約する。
     target が sub 上なら [classified_sub_fixed] に任せ、core 辺を作らない。 *)
  | order_nonadjacent : forall i j s t ps pt,
      nth_error (l ++ sub ++ r) i = Some s ->
      nth_error (l ++ sub ++ r) j = Some t ->
      (S i < j \/ S j < i)%nat ->
      segment_x_ranges_overlap s t ->
      endpoint_of_seg s ps ->
      endpoint_of_seg t pt ->
      ~ onSegmentlist sub pt ->
      snd ps <= snd pt ->
      endpoint_core_step l sub r ps pt.

(* 先頭・末尾に固有の例外順序。傾き保存のための逆向き辺と、
   延長線を介した比較をここに隔離する。 *)
Inductive endpoint_end_step
    (l sub r : list Segment) : Point -> Point -> Prop :=
  (* 北向き・上に凸な先頭では、通常順序の逆も加えて両端を同じ領域にする。 *)
  | order_head_north_cx_reverse : forall hor,
      l <> [] ->
      embed (n, hor, cx) (hd_segment l) ->
      endpoint_end_step l sub r
        (term (hd_segment l)) (init (hd_segment l))
  (* 南向き・下に凸な先頭でも、始点傾き保存のため通常順序の逆を加える。 *)
  | order_head_south_cc_reverse : forall hor,
      l <> [] ->
      embed (s, hor, cc) (hd_segment l) ->
      endpoint_end_step l sub r
        (init (hd_segment l)) (term (hd_segment l))
  (* 北向き・下に凸な末尾では、終点傾き保存のため通常順序の逆を加える。 *)
  | order_last_north_cc_reverse : forall hor,
      r <> [] ->
      embed (n, hor, cc) (last_segment r) ->
      endpoint_end_step l sub r
        (term (last_segment r)) (init (last_segment r))
  (* 南向き・上に凸な末尾でも、通常順序の逆を加えて両端を同じ領域にする。 *)
  | order_last_south_cx_reverse : forall hor,
      r <> [] ->
      embed (s, hor, cx) (last_segment r) ->
      endpoint_end_step l sub r
        (init (last_segment r)) (term (last_segment r))
  (* 同じ x で先頭延長線が末尾延長線以下なら、先頭基点を末尾基点以下にする。 *)
  | order_head_last : forall ph pl,
      onHead_extend (l ++ sub ++ r) ph ->
      onLast_extend (l ++ sub ++ r) pl ->
      fst ph = fst pl ->
      snd ph <= snd pl ->
      endpoint_end_step l sub r
        (init (hd_segment (l ++ sub ++ r)))
        (term (last_segment (l ++ sub ++ r)))
  (* 同じ x で末尾延長線が先頭延長線以下なら、末尾基点を先頭基点以下にする。 *)
  | order_last_head : forall ph pl,
      onHead_extend (l ++ sub ++ r) ph ->
      onLast_extend (l ++ sub ++ r) pl ->
      fst ph = fst pl ->
      snd pl <= snd ph ->
      endpoint_end_step l sub r
        (term (last_segment (l ++ sub ++ r)))
        (init (hd_segment (l ++ sub ++ r)))
  (* 先頭延長線がセグメントより下なら、その基点をセグメントの各端点以下にする。 *)
  | order_head_below_segment : forall seg e q p,
      In seg (l ++ sub ++ r) ->
      onSegment seg e ->
      onHead_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      snd q <= snd e ->
      endpoint_of_seg seg p ->
      endpoint_end_step l sub r
        (init (hd_segment (l ++ sub ++ r))) p
  (* セグメントが先頭延長線より下なら、その各端点を先頭基点以下にする。 *)
  | order_segment_below_head : forall seg e q p,
      In seg (l ++ sub ++ r) ->
      onSegment seg e ->
      onHead_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      snd e <= snd q ->
      endpoint_of_seg seg p ->
      endpoint_end_step l sub r p
        (init (hd_segment (l ++ sub ++ r)))
  (* 末尾延長線がセグメントより下なら、その基点をセグメントの各端点以下にする。 *)
  | order_last_below_segment : forall seg e q p,
      In seg (l ++ sub ++ r) ->
      onSegment seg e ->
      onLast_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      snd q <= snd e ->
      endpoint_of_seg seg p ->
      endpoint_end_step l sub r
        (term (last_segment (l ++ sub ++ r))) p
  (* セグメントが末尾延長線より下なら、その各端点を末尾基点以下にする。 *)
  | order_segment_below_last : forall seg e q p,
      In seg (l ++ sub ++ r) ->
      onSegment seg e ->
      onLast_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      snd e <= snd q ->
      endpoint_of_seg seg p ->
      endpoint_end_step l sub r p
        (term (last_segment (l ++ sub ++ r))).

(* 全順序の一辺は、通常辺か先頭・末尾由来の例外辺のいずれかである。 *)
Inductive endpoint_order_step
    (l sub r : list Segment) : Point -> Point -> Prop :=
  | order_core_step : forall p q,
      endpoint_core_step l sub r p q ->
      endpoint_order_step l sub r p q
  | order_end_step : forall p q,
      endpoint_end_step l sub r p q ->
      endpoint_order_step l sub r p q.

Definition endpoint_order (l sub r : list Segment) : Point -> Point -> Prop :=
  clos_refl_trans Point (endpoint_order_step l sub r).

(* 幾何学的な帰納では、結合木を持つ [clos_refl_trans] よりも、先頭から
   一辺ずつ読めるこの有限パス表示を用いる。 *)
Definition endpoint_order_path
    (l sub r : list Segment) : Point -> Point -> Prop :=
  clos_refl_trans_1n Point (endpoint_order_step l sub r).

Definition endpoint_up_seed
    (l sub r : list Segment) (p : Point) : Prop :=
  endpoint_of (l ++ sub ++ r) p
  /\
  ((exists seg q,
      In seg (nonadjacent_sides l r)
      /\ endpoint_of_seg seg p
      /\ onSegment seg q
      /\ in_sub_x_range sub q
      /\ above_sub_at_x sub q)
   \/ (l <> []
       /\ p = init (hd_segment (l ++ sub ++ r))
       /\ exists q z,
            onHead_extend_strict (l ++ sub ++ r) q
            /\ onSegmentlist sub z
            /\ fst q = fst z
            /\ snd z < snd q)
   \/ (r <> []
       /\ p = term (last_segment (l ++ sub ++ r))
       /\ exists q z,
            onLast_extend_strict (l ++ sub ++ r) q
            /\ onSegmentlist sub z
            /\ fst q = fst z
            /\ snd z < snd q)).

Definition endpoint_down_seed
    (l sub r : list Segment) (p : Point) : Prop :=
  endpoint_of (l ++ sub ++ r) p
  /\
  ((exists seg q,
      In seg (nonadjacent_sides l r)
      /\ endpoint_of_seg seg p
      /\ onSegment seg q
      /\ in_sub_x_range sub q
      /\ below_sub_at_x sub q)
   \/ (l <> []
       /\ p = init (hd_segment (l ++ sub ++ r))
       /\ exists q z,
            onHead_extend_strict (l ++ sub ++ r) q
            /\ onSegmentlist sub z
            /\ fst q = fst z
            /\ snd q < snd z)
   \/ (r <> []
       /\ p = term (last_segment (l ++ sub ++ r))
       /\ exists q z,
            onLast_extend_strict (l ++ sub ++ r) q
            /\ onSegmentlist sub z
            /\ fst q = fst z
            /\ snd q < snd z)).

(* Up seed から順序辺を有限回たどって実際に到達した端点。
   幾何学的不変量を、到達不能な仮想的端点へ要求しないために用いる。 *)
Definition endpoint_up_reachable
    (l sub r : list Segment) (p : Point) : Prop :=
  exists seed,
    endpoint_up_seed l sub r seed
    /\ endpoint_order l sub r seed p.

Definition endpoint_forced_up
    (l sub r : list Segment) (p : Point) : Prop :=
  endpoint_up_reachable l sub r p.

Definition endpoint_forced_down
    (l sub r : list Segment) (p : Point) : Prop :=
  exists seed,
    endpoint_down_seed l sub r seed
    /\ endpoint_order l sub r p seed.

Definition constraint_classifier
    (l sub r : list Segment) (p : Point) : Region :=
  if excluded_middle_informative (onSegmentlist sub p) then RegFix
  else if excluded_middle_informative (endpoint_of (l ++ sub ++ r) p) then
    if excluded_middle_informative (endpoint_forced_up l sub r p) then RegUp
    else if excluded_middle_informative (endpoint_forced_down l sub r p)
         then RegDown else RegFix
  else RegFix.

Definition classify := constraint_classifier.


Definition operate_point
    (l sub r : list Segment) (h : R) (p : Point) : Point :=
  shift h (classify l sub r p) p.
