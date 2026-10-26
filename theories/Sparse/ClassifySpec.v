Require Export Sparse.ClassifyDefinition.
Import ListNotations.

Definition other_than_end (which : CurveEnd) (ls : list Segment) (i : nat) : Prop :=
  match which with HeadEnd => i <> 0%nat | LastEnd => S i <> length ls end.

(* 分類値は移動量の比率。十分大きい倍率の選択は再接続の存在証明の内部で行う。 *)
Record ClassificationSpec (l sub r : list Segment)
    (k : EndpointClassifier) : Prop := {
  (* S0: sub 全体と、左右との共有端点を固定する。 *)
  classified_sub_fixed : forall p, onSegmentlist sub p -> k p = 0;

  (* S1: 高い端点の符号付き変位は低い端点以上である。 *)
  classified_segment_endpoints_monotone : forall seg,
    In seg (l ++ sub ++ r) -> endpoint_displacements_ordered k seg;

  (* S2: 外側の非隣接三角形の境界変位を、その元の上下順に並べる。 *)
  classified_external_segment_order : forall i j s t u v,
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (l ++ sub ++ r) j = Some t ->
    (S i < j \/ S j < i)%nat ->
    In s (l ++ r) -> In t (l ++ r) ->
    onSegment s u -> onSegment t v ->
    fst u = fst v -> snd u < snd v ->
    upper_displacement k s (fst u) <= lower_displacement k t (fst u);

  (* S3: strict 延長線と、その端セグメント以外の全本体を比較する。 *)
  classified_extension_segment_order : forall which i seg e q,
    nth_error (l ++ sub ++ r) i = Some seg ->
    other_than_end which (l ++ sub ++ r) i ->
    onSegment seg e ->
    on_strict_extension which (l ++ sub ++ r) q ->
    fst e = fst q ->
    (snd q < snd e ->
      k (extension_anchor which (l ++ sub ++ r)) <=
        lower_displacement k seg (fst q)) /\
    (snd e < snd q ->
      upper_displacement k seg (fst q) <=
        k (extension_anchor which (l ++ sub ++ r)));

  (* S4: 基点を含む二延長線の上下順序も保存する。 *)
  classified_head_last_extension_order : forall ph pl,
    onHead_extend (l ++ sub ++ r) ph ->
    onLast_extend (l ++ sub ++ r) pl ->
    fst ph = fst pl ->
    (snd ph < snd pl ->
      k (init (hd_segment (l ++ sub ++ r))) <=
        k (term (last_segment (l ++ sub ++ r)))) /\
    (snd pl < snd ph ->
      k (term (last_segment (l ++ sub ++ r))) <=
        k (init (hd_segment (l ++ sub ++ r))));

  (* S5: 各三角形で退避側を一つ選び、共通閉 x 区間の両端を検査する。
     零の変位は、その断面が元から退避側にある場合だけ許す。 *)
  classified_segment_escape : forall seg,
    In seg (nonadjacent_sides l r) ->
    (forall x, sub_overlap_endpoint sub seg x ->
      0 <= lower_displacement k seg x /\
      (lower_displacement k seg x = 0 ->
        ry1 (rect_of sub) < triangle_lower seg x)) \/
    (forall x, sub_overlap_endpoint sub seg x ->
      upper_displacement k seg x <= 0 /\
      (upper_displacement k seg x = 0 ->
        triangle_upper seg x < ry0 (rect_of sub)));

  (* S6: 動かさない外側延長線は、既に sub の閉長方形を避けている。 *)
  classified_fixed_extension_clear : forall which,
    external_end_nonempty which l r ->
    k (extension_anchor which (l ++ sub ++ r)) = 0 ->
    forall p, on_strict_extension which (l ++ sub ++ r) p ->
      ~ in_rect_or_endpoints_at sub p;

  (* S7: 大きい全ての倍率で、先頭の始点傾きと末尾の終点傾きを指定できる。 *)
  classified_end_slopes : exists h0, 0 <= h0 /\
    forall h, h0 <= h ->
    (l <> [] ->
      reconnect_init_slope
        (move_point (scale_classifier h k) (init (hd_segment l)))
        (move_point (scale_classifier h k) (term (hd_segment l)))
        (orn_seg (hd_segment l)) (slope_init (hd_segment l))) /\
    (r <> [] ->
      reconnect_term_slope
        (move_point (scale_classifier h k) (init (last_segment r)))
        (move_point (scale_classifier h k) (term (last_segment r)))
        (orn_seg (last_segment r)) (slope_term (last_segment r)))
}.
