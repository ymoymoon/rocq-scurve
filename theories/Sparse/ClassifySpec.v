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

(* 本体上の比較点 e と延長線点 q の上下順序を、両端点と延長線基点の領域へ移す。
   比較を要求する範囲は PMP・PPMM の各仕様で指定する。 *)
Definition segment_extension_order
    (classifier : EndpointClassifier) (seg : Segment) (g : Region)
    (e q : Point) : Prop :=
  (snd q < snd e ->
     region_at_or_above (classifier (init seg)) g /\
     region_at_or_above (classifier (term seg)) g)
  /\
  (snd e < snd q ->
     region_at_or_above g (classifier (init seg)) /\
     region_at_or_above g (classifier (term seg))).

(* PMP・PPMM に共通する固定・端点移動・延長線の順序と傾きの仕様。 *)
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
        classifier h (last_segment r);

  (* sub の x 範囲を通る非隣接セグメントでは、両端を同じ領域にする。
     その領域を Fix にできるか、どちらへ動かすかは各仕様で指定する。 *)
  classified_segment_at_sub_x_uniform : forall seg p,
    In seg (nonadjacent_sides l r) -> onSegment seg p ->
    in_sub_x_range sub p -> classifier (init seg) = classifier (term seg)
}.

(* 先頭・末尾の延長線を、基点と strict な半直線で一様に扱う。 *)
Inductive CurveEnd := HeadEnd | LastEnd.

Definition extension_anchor (which : CurveEnd) (ls : list Segment) : Point :=
  match which with
  | HeadEnd => init (hd_segment ls)
  | LastEnd => term (last_segment ls)
  end.

Definition on_strict_extension (which : CurveEnd) (ls : list Segment) : Point -> Prop :=
  match which with
  | HeadEnd => onHead_extend_strict ls
  | LastEnd => onLast_extend_strict ls
  end.

Definition external_end_nonempty (which : CurveEnd) (l r : list Segment) : Prop :=
  match which with HeadEnd => l <> [] | LastEnd => r <> [] end.

(* PMP 用：共通の端点移動に加え、全域の順序と Plus 三角形からの上方退避を要求する。 *)
Record PMPClassificationSpec
    (l sub r : list Segment) {classifier : EndpointClassifier} : Prop := {
  pmp_endpoint_spec :> @EndpointMovementSpec l sub r classifier;

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

  (* 両端の延長線と一セグメントの上下順序を三つの端点分類へ移す。 *)
  classified_extension_segment_order :
    forall which seg e q,
      In seg (l ++ sub ++ r) ->
      onSegment seg e ->
      on_strict_extension which (l ++ sub ++ r) q ->
      fst e = fst q ->
      segment_extension_order classifier seg
        (classifier (extension_anchor which (l ++ sub ++ r))) e q;

  (* 分類は上移動または固定の二択。 *)
  pmp_only_up_or_fix : forall p, classifier p = RegUp \/ classifier p = RegFix;

  (* 退避方向は入力側の Plus 三角形との接触から決める。 *)
  pmp_triangle_meeting_moves_up : forall seg p,
    In seg (nonadjacent_sides l r) ->
    in_segment_triangle seg p -> in_sub_triangle Plus sub p ->
    classifier (init seg) = RegUp /\ classifier (term seg) = RegUp;
    
  (* 外側の延長線が目的三角形に入るとき、その基点を上げる。 *)
  pmp_extension_meeting_moves_up : forall which,
    external_end_nonempty which l r -> forall p,
    on_strict_extension which (l ++ sub ++ r) p -> in_sub_triangle Plus sub p ->
    classifier (extension_anchor which (l ++ sub ++ r)) = RegUp
}.

(* PPMM・PM 用：外側の順序を保存し、sub 長方形からは上下へ退避する。 *)
Record ClassificationSpec
    (l sub r : list Segment) {classifier : EndpointClassifier} : Prop := {
  classification_endpoint_spec :> @EndpointMovementSpec l sub r classifier;

  (* 外側の非隣接セグメントが同じ x で上下に並ぶとき、その全端点の
     移動方向も同じ順序にする。疎性と合わせて閉三角形の順序も導ける。 *)
  classified_external_segment_order :
    forall i j s t ps pt u v,
      nth_error (l ++ sub ++ r) i = Some s ->
      nth_error (l ++ sub ++ r) j = Some t ->
      (S i < j \/ S j < i)%nat ->
      In s (l ++ r) -> In t (l ++ r) ->
      endpoint_of_seg s ps ->
      endpoint_of_seg t pt ->
      onSegment s u ->
      onSegment t v ->
      fst u = fst v ->
      snd u < snd v ->
      region_at_or_above (classifier pt) (classifier ps);

  (* 両端の延長線について、外側とは常に比較する。
     sub との比較だけ、当該延長線点が gap 内なら外す。 *)
  classified_extension_segment_order_outside_gap :
    forall which seg e q,
      (In seg (l ++ r) \/
       (In seg sub /\ avoids_sub_vertical_gap sub q)) ->
      onSegment seg e ->
      on_strict_extension which (l ++ sub ++ r) q ->
      fst e = fst q ->
      segment_extension_order classifier seg
        (classifier (extension_anchor which (l ++ sub ++ r))) e q;

  (* 共通の両端同領域条件に加え、PPMM では Fix を除いて上下へ退避させる。 *)
  classified_segment_at_sub_x_moves :
    forall seg p,
      In seg (nonadjacent_sides l r) ->
      onSegment seg p ->
      in_sub_x_range sub p ->
      classifier (init seg) <> RegFix;

  (* 外側の strict 延長線が sub の閉 x 範囲へ入るなら、その基点を動かす。 *)
  classified_extension_at_sub_x :
    forall which,
      external_end_nonempty which l r ->
      forall p,
        on_strict_extension which (l ++ sub ++ r) p ->
        in_sub_x_range sub p ->
        classifier (extension_anchor which (l ++ sub ++ r)) = RegUp
        \/ classifier (extension_anchor which (l ++ sub ++ r)) = RegDown
}.
