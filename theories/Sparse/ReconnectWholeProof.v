Require Export Sparse.ReconnectLocalProof.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.

(* 交わらない閉三角形の上下順序は、同じ x にあるセグメント上の点にも移る。 *)
Lemma disjoint_triangle_order_has_segment_witnesses : forall s t u v,
  (forall p, in_segment_triangle s p -> ~ in_segment_triangle t p) ->
  in_segment_triangle s u -> in_segment_triangle t v ->
  fst u = fst v -> snd u < snd v ->
  exists a b,
    onSegment s a /\ onSegment t b /\ fst a = fst b /\ snd a < snd b.
Proof.
  intros s t u v Hdisjoint Hu Hv Hx Hy.
  destruct (segment_has_point_at_x s (fst u) (proj1 (proj1 Hu)))
    as [a [Ha Hax]].
  destruct (segment_has_point_at_x t (fst v) (proj1 (proj1 Hv)))
    as [b [Hb Hbx]].
  pose proof (segment_in_endpoint_triangle s a Ha) as Hta.
  pose proof (segment_in_endpoint_triangle t b Hb) as Htb.
  assert (HvOutside : ~ in_segment_triangle s v).
  { intro H. exact (Hdisjoint v H Hv). }
  pose proof (proj2 (triangle_outside_vertical_order s v u a Hu Hta
    ltac:(congruence) ltac:(congruence) HvOutside) Hy) as Hav.
  pose proof (proj1 (triangle_outside_vertical_order t a v b Hv Htb
    ltac:(congruence) ltac:(congruence) (Hdisjoint a Hta)) Hav) as Hab.
  exists a, b. repeat split; try assumption. congruence.
Qed.

Module ReconnectWholeByClassifier.
Section WithClassifier.
Variable classify : list Segment -> list Segment -> list Segment -> EndpointClassifier.

Local Notation operate_point := (ReconnectByClassifier.operate_point classify).
Local Notation operate_point_fst := (ReconnectLocalByClassifier.operate_point_fst classify).
Local Notation reconnectable_after := (ReconnectByClassifier.reconnectable_after classify).
Local Notation reconnect_slope_after := (ReconnectByClassifier.reconnect_slope_after classify).
Local Notation reconnect_init_slope_after := (ReconnectByClassifier.reconnect_init_slope_after classify).
Local Notation reconnect_term_slope_after := (ReconnectByClassifier.reconnect_term_slope_after classify).
Local Notation head_init_slope_after := (ReconnectByClassifier.head_init_slope_after classify).
Local Notation last_term_slope_after := (ReconnectByClassifier.last_term_slope_after classify).
Local Notation all_reconnectable := (ReconnectByClassifier.all_reconnectable classify).
Local Notation reconnect_one := (ReconnectByClassifier.reconnect_one classify).
Local Notation reconnect_segs := (ReconnectByClassifier.reconnect_segs classify).
Local Notation reconnect_whole := (ReconnectByClassifier.reconnect_whole classify).
Local Notation reconnect_one_endpoints_orn := (ReconnectLocalByClassifier.reconnect_one_endpoints_orn classify).
Local Notation reconnect_one_init := (ReconnectLocalByClassifier.reconnect_one_init classify).
Local Notation reconnect_one_term := (ReconnectLocalByClassifier.reconnect_one_term classify).
Local Notation reconnect_one_orn := (ReconnectLocalByClassifier.reconnect_one_orn classify).
Local Notation reconnect_one_head_slope_init := (ReconnectLocalByClassifier.reconnect_one_head_slope_init classify).
Local Notation reconnect_one_last_slope_term := (ReconnectLocalByClassifier.reconnect_one_last_slope_term classify).
Local Notation reconnect_one_head_extension_preimage := (ReconnectLocalByClassifier.reconnect_one_head_extension_preimage classify).
Local Notation reconnect_one_last_extension_preimage := (ReconnectLocalByClassifier.reconnect_one_last_extension_preimage classify).
Local Notation reconnect_head_extension_preimage_from_spec := (ReconnectLocalByClassifier.reconnect_head_extension_preimage_from_spec classify).
Local Notation reconnect_last_extension_preimage_from_spec := (ReconnectLocalByClassifier.reconnect_last_extension_preimage_from_spec classify).
Local Notation reconnect_head_strict_extension_preimage_from_spec := (ReconnectLocalByClassifier.reconnect_head_strict_extension_preimage_from_spec classify).
Local Notation reconnect_last_strict_extension_preimage_from_spec := (ReconnectLocalByClassifier.reconnect_last_strict_extension_preimage_from_spec classify).
Local Notation reconnect_segs_length := (ReconnectLocalByClassifier.reconnect_segs_length classify).
Local Notation reconnect_segs_nth_error := (ReconnectLocalByClassifier.reconnect_segs_nth_error classify).
Local Notation operation_height_safe_from_spec := (ReconnectLocalByClassifier.operation_height_safe_from_spec classify).
Local Notation operated_segment_axis_orders_from_spec := (ReconnectLocalByClassifier.operated_segment_axis_orders_from_spec classify).
Local Notation operate_endpoints_reconnectable_from_spec := (ReconnectLocalByClassifier.operate_endpoints_reconnectable_from_spec classify).
Local Notation reconnect_whole_nth_spec := (ReconnectLocalByClassifier.reconnect_whole_nth_spec classify).
Local Notation reconnect_whole_connected := (ReconnectLocalByClassifier.reconnect_whole_connected classify).
Local Notation prepared_reconnect_whole_preserves_embed := (ReconnectLocalByClassifier.prepared_reconnect_whole_preserves_embed classify).
Local Notation reconnect_whole_length := (ReconnectLocalByClassifier.reconnect_whole_length classify).
Local Notation operated_nonadjacent_endpoints_separated_from_spec := (ReconnectLocalByClassifier.operated_nonadjacent_endpoints_separated_from_spec classify).
Local Notation classified_shifted_extension_avoids_sub_rect_from_spec := (ReconnectLocalByClassifier.classified_shifted_extension_avoids_sub_rect_from_spec classify).

(* 局所補題を組み合わせ、再接続後の曲線全体の疎性を示す。 *)

Lemma split_nonadjacent_nth_errors : forall ls l s r t,
  ls = l ++ [s] ++ r ->
  In t (nonadjacent_sides l r) ->
  exists i j,
    nth_error ls i = Some s /\ nth_error ls j = Some t
    /\ (S i < j \/ S j < i)%nat.
Proof.
  intros ls l s r t Hsplit Hin. subst ls.
  assert (Hs : nth_error (l ++ [s] ++ r) (length l) = Some s).
  { rewrite nth_error_app2 by lia. replace (length l - length l)%nat with 0%nat by lia.
    reflexivity. }
  unfold nonadjacent_sides in Hin. rewrite in_app_iff in Hin.
  destruct Hin as [Hin | Hin].
  - induction l using rev_ind.
    + simpl in Hin. contradiction.
    + rewrite removelast_last in Hin.
      destruct (In_nth_error l t Hin) as [j Hj].
      assert (Hjlt : (j < length l)%nat).
      { now apply nth_error_Some; rewrite Hj. }
      exists (length (l ++ [x])), j. repeat split.
      * change (nth_error ((l ++ [x]) ++ ([s] ++ r)) (length (l ++ [x])) = Some s).
        rewrite nth_error_app2 by lia.
        replace (length (l ++ [x]) - length (l ++ [x]))%nat with 0%nat by lia.
        reflexivity.
      * assert (Hprefix : nth_error (l ++ [x]) j = Some t).
        { rewrite nth_error_app1 by exact Hjlt. exact Hj. }
        eapply eq_trans.
        -- apply nth_error_app1. rewrite length_app. simpl. lia.
        -- exact Hprefix.
      * right. rewrite length_app. simpl. lia.
  - destruct r as [|a r]; [simpl in Hin; contradiction|].
    simpl in Hin.
    destruct (In_nth_error r t Hin) as [j Hj].
    exists (length l), (length l + 2 + j)%nat. repeat split.
    + exact Hs.
    + rewrite nth_error_app2 by lia.
      replace (length l + 2 + j - length l)%nat with (S (S j)) by lia.
      simpl. exact Hj.
    + left. lia.
Qed.

Lemma nth_error_exists_at_equal_length : forall (xs ys : list Segment) i y,
  length xs = length ys ->
  nth_error ys i = Some y ->
  exists x, nth_error xs i = Some x.
Proof.
  intros xs ys i y Hlen Hy.
  assert (Hi : (i < length xs)%nat).
  { rewrite Hlen. now apply nth_error_lt in Hy. }
  destruct (nth_error xs i) as [x |] eqn:Hx; [now exists x |].
  exfalso. apply (proj2 (nth_error_Some xs i) Hi). exact Hx.
Qed.

Definition region_delta (h : R) (g : Region) : R :=
  match g with RegFix => 0 | RegUp => h | RegDown => -h end.

Lemma region_delta_order : forall h g0 g1,
  0 <= h -> region_at_or_above g1 g0 ->
  region_delta h g0 <= region_delta h g1.
Proof.
  intros h g0 g1 Hh [Heq | Habove]; [subst; apply Rle_refl |].
  destruct Habove; unfold region_delta; lra.
Qed.

Lemma shift_y_delta : forall h g p,
  snd (shift h g p) - snd p = region_delta h g.
Proof.
  intros h g [x y]. destruct g; unfold shift, region_delta; simpl; lra.
Qed.

(* 十分大きな移動後、全体の延長線は sub の長方形を避ける。 *)
Lemma reconnect_extensions_avoid_sub_rect_from_spec :
  forall l sub r h p,
    sub <> [] ->
    connected sub ->
    @ClassificationSpec l sub r (classify l sub r) ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    ((l <> [] /\ onHead_extend_strict (reconnect_whole l sub r h) p)
     \/ (r <> [] /\ onLast_extend_strict (reconnect_whole l sub r h) p)) ->
    ~ in_rect_or_endpoints_at sub p.
Proof.
  intros l sub r h p Hne HconnSub Hspec Hh Hsparse Hextend.
  assert (Hpreimage : exists which q,
    external_end_nonempty which l r /\
    on_strict_extension which (l ++ sub ++ r) q /\
    p = shift h (classify l sub r (extension_anchor which (l ++ sub ++ r))) q).
  { destruct Hextend as [[Hl Hhead] | [Hr Hlast]].
    - destruct (reconnect_head_strict_extension_preimage_from_spec
                l sub r h p Hne Hsparse Hspec
                (Rlt_le _ _ (proj1 Hh)) Hhead)
        as [q [Hq Hshift]].
      exists HeadEnd, q. repeat split; assumption.
    - destruct (reconnect_last_strict_extension_preimage_from_spec
                l sub r h p Hne Hsparse Hspec
                (Rlt_le _ _ (proj1 Hh)) Hlast)
        as [q [Hq Hshift]].
      exists LastEnd, q. repeat split; assumption. }
  destruct Hpreimage as [which [q [Hend [Hq Hshift]]]].
  set (g := classify l sub r (extension_anchor which (l ++ sub ++ r))).
  eapply (classified_shifted_extension_avoids_sub_rect_from_spec
            l sub r h p q g Hne HconnSub Hspec Hh).
  - destruct which; [now left | now right].
  - intros Hg z [s [Hs Hz]] Hx Hy Hgap. exfalso.
    pose proof (proj1
      (classified_extension_segment_order_outside_gap l sub r Hspec which
         s z q (or_intror (conj Hs Hgap)) Hz Hq ltac:(symmetry; exact Hx)) Hy)
      as [HinitOrder _].
    change (classify l sub r (extension_anchor which (l ++ sub ++ r)) = RegUp)
      in Hg.
    rewrite Hg in HinitOrder.
    pose proof (region_at_or_above_RegUp_inv _ HinitOrder) as HinitUp.
    pose proof (classified_sub_fixed l sub r Hspec (init s)
      ltac:(exists s; split; [exact Hs | apply onInit])) as HinitFix.
    congruence.
  - intros Hg z [s [Hs Hz]] Hx Hy Hgap. exfalso.
    pose proof (proj2
      (classified_extension_segment_order_outside_gap l sub r Hspec which
         s z q (or_intror (conj Hs Hgap)) Hz Hq ltac:(symmetry; exact Hx)) Hy)
      as [HinitOrder _].
    change (classify l sub r (extension_anchor which (l ++ sub ++ r)) = RegDown)
      in Hg.
    rewrite Hg in HinitOrder.
    pose proof (RegDown_at_or_above_inv _ HinitOrder) as HinitDown.
    pose proof (classified_sub_fixed l sub r Hspec (init s)
      ltac:(exists s; split; [exact Hs | apply onInit])) as HinitFix.
    congruence.
  - intros Hx. exact (classified_extension_at_sub_x l sub r Hspec which Hend q Hq Hx).
  - exact Hshift.
Qed.

(* 新しい閉三角形の点を、同じ出現の旧三角形へ引き戻す。 *)
Lemma reconnected_triangle_preimage :
  forall l sub r h i s s' z,
    @EndpointMovementSpec l sub r (classify l sub r) ->
    h_large h sub ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (reconnect_whole l sub r h) i = Some s' ->
    in_segment_triangle s' z ->
    exists u,
      in_segment_triangle s u /\ fst u = fst z /\
      Rmin (region_delta h (classify l sub r (init s)))
           (region_delta h (classify l sub r (term s))) <=
        snd z - snd u <=
      Rmax (region_delta h (classify l sub r (init s)))
           (region_delta h (classify l sub r (term s))).
Proof.
  intros l sub r h i s s' z Hspec Hh Hold Hnew Hz.
  assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
  { exact (operate_endpoints_reconnectable_from_spec l sub r h Hspec Hh). }
  destruct (reconnect_whole_nth_spec l sub r h i s s' Hspec Hrec Hold Hnew)
    as [Horn [Hinit Hterm]].
  assert (Hin : In s (l ++ sub ++ r)) by now apply nth_error_In in Hold.
  destruct (operated_segment_axis_orders_from_spec
              l sub r h s Hspec (proj1 Hh) Hin) as [Hx Hy].
  rewrite <- Hinit, <- Hterm in Hx, Hy.
  assert (Hprimitive : primitive_segment s' = primitive_segment s).
  { exact (same_primitive_of_axis_orders s s' Hx Hy Horn). }
  assert (Hix : init_x s' = init_x s).
  { unfold init_x. rewrite Hinit. apply operate_point_fst. }
  assert (Htx : term_x s' = term_x s).
  { unfold term_x. rewrite Hterm. apply operate_point_fst. }
  assert (Hsign :
    0 < (term_y s - init_y s) * (term_y s' - init_y s')).
  { unfold init_y, term_y in *.
    destruct (Rlt_dec (snd (init s)) (snd (term s))) as [Hup | Hnotup].
    - pose proof (proj1 Hy Hup) as Hup'. nra.
    - assert (Hdown : snd (term s) < snd (init s)).
      { pose proof (neq_init_term_y s). unfold init_y, term_y in *. nra. }
      assert (Hdown' : snd (term s') < snd (init s')).
      { pose proof (neq_init_term_y s'). unfold init_y, term_y in *.
        destruct (Rlt_dec (snd (init s')) (snd (term s')))
          as [Hnewup | Hnewnotup]; [apply (proj2 Hy) in Hnewup; lra |].
        nra. }
      nra. }
  destruct (triangle_vertical_shift_preimage s s' z Hix Htx
              ltac:(now rewrite Hprimitive) Hsign Hz)
    as [u [Hu [Hux Hbounds]]].
  exists u. split; [exact Hu |]. split; [exact Hux |].
  assert (Hdi : init_y s' - init_y s =
    region_delta h (classify l sub r (init s))).
  { unfold init_y. rewrite Hinit. unfold operate_point.
    apply shift_y_delta. }
  assert (Hdt : term_y s' - term_y s =
    region_delta h (classify l sub r (term s))).
  { unfold term_y. rewrite Hterm. unfold operate_point.
    apply shift_y_delta. }
  now rewrite <- Hdi, <- Hdt.
Qed.

Lemma classified_triangle_delta_order :
  forall l sub r h i j s t u v,
    @PMPClassificationSpec l sub r (classify l sub r) ->
    0 <= h ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (l ++ sub ++ r) j = Some t ->
    (S i < j \/ S j < i)%nat ->
    in_segment_triangle s u ->
    in_segment_triangle t v ->
    fst u = fst v ->
    snd u < snd v ->
    Rmax (region_delta h (classify l sub r (init s)))
         (region_delta h (classify l sub r (term s))) <=
    Rmin (region_delta h (classify l sub r (init t)))
         (region_delta h (classify l sub r (term t))).
Proof.
  intros l sub r h i j s t u v Hspec Hh
    Hs Ht Hfar Hu Hv Hx Hy.
  assert (Horders :
    forall ps pt,
      endpoint_of_seg s ps -> endpoint_of_seg t pt ->
      region_delta h (classify l sub r ps) <=
      region_delta h (classify l sub r pt)).
  { intros ps pt Hps Hpt.
    apply region_delta_order; [exact Hh |].
    exact (classified_nonadjacent_triangle_order l sub r Hspec
      i j s t ps pt u v Hs Ht Hfar Hps Hpt Hu Hv Hx Hy). }
  pose proof (Horders (init s) (init t) (or_introl eq_refl)
                (or_introl eq_refl)) as Hii.
  pose proof (Horders (init s) (term t) (or_introl eq_refl)
                (or_intror eq_refl)) as Hit.
  pose proof (Horders (term s) (init t) (or_intror eq_refl)
                (or_introl eq_refl)) as Hti.
  pose proof (Horders (term s) (term t) (or_intror eq_refl)
                (or_intror eq_refl)) as Htt.
  unfold Rmin, Rmax. repeat destruct Rle_dec; lra.
Qed.

(* 旧三角形の外側の点が、その縦断面との上下順序に従って動くなら、
   再接続後の三角形にも入らない。先頭・末尾の延長線で共用する。 *)
Lemma shifted_point_avoids_reconnected_triangle :
  forall l sub r h i s s' q z g,
    @EndpointMovementSpec l sub r (classify l sub r) ->
    h_large h sub ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (reconnect_whole l sub r h) i = Some s' ->
    ~ in_segment_triangle s q ->
    z = shift h g q ->
    (forall e,
       onSegment s e -> fst e = fst q ->
       segment_extension_order (classify l sub r) s g e q) ->
    ~ in_segment_triangle s' z.
Proof.
  intros l sub r h i s s' q z g Hspec Hh Hold Hnew Houtside
    Hshift Horder Hz.
  destruct (reconnected_triangle_preimage
              l sub r h i s s' z Hspec Hh Hold Hnew Hz)
    as [u [Hu [Hux Hbounds]]].
  assert (Hqz : fst q = fst z).
  { subst z. destruct g; reflexivity. }
  assert (Hqu : fst q = fst u) by congruence.
  assert (Hqx : rx0 (rect_of [s]) <= fst q <= rx1 (rect_of [s])).
  { destruct Hu as [[Hx _] _]. rewrite Hqu. exact Hx. }
  destruct (segment_has_point_at_x s (fst q) Hqx)
    as [e [He Hex]].
  assert (HtriE : in_segment_triangle s e).
  { now apply segment_in_endpoint_triangle. }
  destruct (triangle_outside_vertical_order
              s q u e Hu HtriE Hqu ltac:(symmetry; exact Hex) Houtside)
    as [Hbelow Habove].
  assert (Hneq : snd q <> snd u).
  { intros Hy. apply Houtside.
    destruct q as [xq yq], u as [xu yu]; simpl in *; congruence. }
  assert (Hdy : snd z - snd q = region_delta h g).
  { subst z. apply shift_y_delta. }
  destruct (Rlt_dec (snd q) (snd u)) as [Hlower | Hlower].
  - destruct (proj1 (Horder e He Hex) (Hbelow Hlower))
      as [Hinit Hterm].
    pose proof (region_delta_order h g (classify l sub r (init s))
                  (Rlt_le _ _ (proj1 Hh)) Hinit) as Hdi.
    pose proof (region_delta_order h g (classify l sub r (term s))
                  (Rlt_le _ _ (proj1 Hh)) Hterm) as Hdt.
    unfold Rmin, Rmax in *. repeat destruct Rle_dec; lra.
  - assert (Hupper : snd u < snd q) by lra.
    destruct (proj2 (Horder e He Hex) (Habove Hupper))
      as [Hinit Hterm].
    pose proof (region_delta_order h (classify l sub r (init s)) g
                  (Rlt_le _ _ (proj1 Hh)) Hinit) as Hdi.
    pose proof (region_delta_order h (classify l sub r (term s)) g
                  (Rlt_le _ _ (proj1 Hh)) Hterm) as Hdt.
    unfold Rmin, Rmax in *. repeat destruct Rle_dec; lra.
Qed.

(* 端点移動と再接続後も、非隣接出現の閉三角形は交わらない。
   旧証明の外接長方形分離は三角形疎性から従わない。 *)
Lemma reconnect_preserves_triangle_separation_prepared :
  forall ds l sub r h,
    sub <> [] ->
    @PMPClassificationSpec l sub r (classify l sub r) ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    segment_triangles_separated (reconnect_whole l sub r h).
Proof.
  intros ds l sub r h Hne Hspec Hh Hsparse _ _
    ls s' rs Hsplit t' z Hin HzT HzS.
  destruct (split_nonadjacent_nth_errors
              (reconnect_whole l sub r h) ls s' rs t' Hsplit Hin)
    as [i [j [HnewS [HnewT Hfar]]]].
  assert (Hlen : length (l ++ sub ++ r) =
                 length (reconnect_whole l sub r h)).
  { symmetry. apply reconnect_whole_length. }
  destruct (nth_error_exists_at_equal_length
              (l ++ sub ++ r) (reconnect_whole l sub r h) i s'
              Hlen HnewS) as [s Hs].
  destruct (nth_error_exists_at_equal_length
              (l ++ sub ++ r) (reconnect_whole l sub r h) j t'
              Hlen HnewT) as [t Ht].
  destruct (reconnected_triangle_preimage
              l sub r h i s s' z Hspec Hh Hs HnewS HzS)
    as [u [Hu [Hux Hus]]].
  destruct (reconnected_triangle_preimage
              l sub r h j t t' z Hspec Hh Ht HnewT HzT)
    as [v [Hv [Hvx Hvs]]].
  assert (Hneq : snd u <> snd v).
  { intros Hy.
    assert (Heq : u = v).
    { destruct u as [xu yu], v as [xv yv]; simpl in *; congruence. }
    destruct (nth_error_far_in_nonadjacent_sides
                (l ++ sub ++ r) i j s t Hs Ht Hfar)
      as [lo [ro [HsplitOld Htin]]].
    subst v.
    exact ((proj2 (Hsparse lo s ro HsplitOld)) t u Htin Hv Hu). }
  destruct (Rlt_dec (snd u) (snd v)) as [Huv | Huv].
  - pose proof (classified_triangle_delta_order
      l sub r h i j s t u v Hspec (Rlt_le _ _ (proj1 Hh))
      Hs Ht Hfar Hu Hv ltac:(transitivity (fst z); [exact Hux | symmetry; exact Hvx])
      Huv) as Horder.
    unfold Rmin, Rmax in *. repeat destruct Rle_dec; lra.
  - assert (Hvu : snd v < snd u) by lra.
    pose proof (classified_triangle_delta_order
      l sub r h j i t s v u Hspec (Rlt_le _ _ (proj1 Hh))
      Ht Hs ltac:(lia) Hv Hu
      ltac:(transitivity (fst z); [exact Hvx | symmetry; exact Hux])
      Hvu) as Horder.
    unfold Rmin, Rmax in *. repeat destruct Rle_dec; lra.
Qed.

(* strict 延長線は、再接続後も外側セグメントの閉三角形を避ける。 *)
Lemma reconnect_preserves_triangle_extension_avoidance_prepared :
  forall ds l sub r h,
    sub <> [] ->
    @PMPClassificationSpec l sub r (classify l sub r) ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    extensions_avoid_segment_triangles (reconnect_whole l sub r h).
Proof.
  intros ds l sub r h Hne Hspec Hh Hsparse _ _
    ls s' rs Hsplit p Hextend.
  assert (Hnew : nth_error (reconnect_whole l sub r h) (length ls) = Some s').
  { rewrite Hsplit. rewrite nth_error_app2 by lia.
    replace (length ls - length ls)%nat with 0%nat by lia.
    reflexivity. }
  assert (Hlen : length (l ++ sub ++ r) =
                 length (reconnect_whole l sub r h)).
  { symmetry. apply reconnect_whole_length. }
  destruct (nth_error_exists_at_equal_length
              (l ++ sub ++ r) (reconnect_whole l sub r h)
              (length ls) s' Hlen Hnew) as [s Hold].
  destruct (@nth_error_split Segment (l ++ sub ++ r)
              (length ls) s Hold) as [lo [ro [HsplitOld HloLen]]].
  assert (Hin : In s (l ++ sub ++ r)) by now apply nth_error_In in Hold.
  destruct Hextend as [[Hls Hhead] | [Hrs Hlast]].
  - destruct (reconnect_head_strict_extension_preimage_from_spec
                l sub r h p
                Hne
                Hsparse Hspec (Rlt_le _ _ (proj1 Hh)) Hhead)
      as [q [Hq Hshift]].
    assert (Hlo : lo <> []).
    { intros Heq. subst lo. simpl in HloLen.
      destruct ls; [contradiction | simpl in HloLen; lia]. }
    assert (Houtside : ~ in_segment_triangle s q).
    { exact ((proj1 (Hsparse lo s ro HsplitOld)) q
        (or_introl (conj Hlo Hq))). }
    eapply (shifted_point_avoids_reconnected_triangle
      l sub r h (length ls) s s' q p
      (classify l sub r (init (hd_segment (l ++ sub ++ r)))))
      ; try eassumption; try exact (pmp_endpoint_spec l sub r Hspec).
    intros e He Hx.
    exact (classified_extension_segment_order
      l sub r Hspec HeadEnd s e q Hin He Hq Hx).
  - destruct (reconnect_last_strict_extension_preimage_from_spec
                l sub r h p
                Hne
                Hsparse Hspec (Rlt_le _ _ (proj1 Hh)) Hlast)
      as [q [Hq Hshift]].
    assert (Hro : ro <> []).
    { intros Heq. subst ro.
      assert (HlengthNew :
        length (reconnect_whole l sub r h) =
        (length ls + 1 + length rs)%nat).
      { rewrite Hsplit. repeat rewrite length_app. simpl. lia. }
      assert (HlengthOld :
        length (l ++ sub ++ r) = (length lo + 1)%nat).
      { rewrite HsplitOld. repeat rewrite length_app. simpl. lia. }
      destruct rs; [contradiction | simpl in *; lia]. }
    assert (Houtside : ~ in_segment_triangle s q).
    { exact ((proj1 (Hsparse lo s ro HsplitOld)) q
        (or_intror (conj Hro Hq))). }
    eapply (shifted_point_avoids_reconnected_triangle
      l sub r h (length ls) s s' q p
      (classify l sub r (term (last_segment (l ++ sub ++ r)))))
      ; try eassumption; try exact (pmp_endpoint_spec l sub r Hspec).
    intros e He Hx.
    exact (classified_extension_segment_order
      l sub r Hspec LastEnd s e q Hin He Hq Hx).
Qed.

(* 蓋や局所退避条件ではなく、共通の三角形順序だけから全域疎性を保存する。 *)
Lemma reconnect_preserves_sparse_embedding_from_spec :
  forall ds l sub r h,
    sub <> [] ->
    @PMPClassificationSpec l sub r (classify l sub r) ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    sparse_embedding (reconnect_whole l sub r h).
Proof.
  intros ds l sub r h Hne Hspec Hh Hsparse Hembed Hext.
  apply geometric_triangle_sparse_embedding.
  - exact (reconnect_preserves_triangle_separation_prepared
             ds l sub r h Hne Hspec Hh Hsparse Hembed Hext).
  - exact (reconnect_preserves_triangle_extension_avoidance_prepared
             ds l sub r h Hne Hspec Hh Hsparse Hembed Hext).
Qed.

(* 分類仕様の延長線順序を使い、再接続後の延長線非交差を示す。 *)
Lemma ordinary_extensions_disjoint_prepared :
  forall ds l sub r h,
    sub <> [] ->
    @EndpointMovementSpec l sub r (classify l sub r) ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    extensions_disjoint (reconnect_whole l sub r h).
Proof.
  intros ds l sub r h Hne Hspec Hh Hsparse Hembed Hext.
  assert (HheadSlope :
      l <> [] -> reconnect_init_slope_after l sub r h (hd_segment l)).
  { intros Hl. unfold reconnect_init_slope_after, operate_point.
    exact (classified_head_init_slope_reconnectable
             l sub r Hspec h (Rlt_le _ _ (proj1 Hh)) Hl). }
  assert (HlastSlope :
      r <> [] -> reconnect_term_slope_after l sub r h (last_segment r)).
  { intros Hr. unfold reconnect_term_slope_after, operate_point.
    exact (classified_last_term_slope_reconnectable
             l sub r Hspec h (Rlt_le _ _ (proj1 Hh)) Hr). }
  intros p Hhead Hlast.
  destruct (reconnect_head_extension_preimage_from_spec
              l sub r h p
              Hne
              Hspec HheadSlope Hhead)
    as [ph [Hph HshiftHead]].
  destruct (reconnect_last_extension_preimage_from_spec
              l sub r h p
              Hne
              Hspec Hsparse HlastSlope Hlast)
    as [pl [Hpl HshiftLast]].
  assert (Hx : fst ph = fst pl).
  { assert (HheadX : fst p = fst ph).
    { rewrite HshiftHead, shift_fst. reflexivity. }
    assert (HlastX : fst p = fst pl).
    { rewrite HshiftLast, shift_fst. reflexivity. }
    lra. }
  assert (Hneq : ph <> pl).
  { intro Heq. subst pl. exact (Hext ph Hph Hpl). }
  pose proof (classified_head_last_extension_order
                l sub r Hspec ph pl Hph Hpl Hx)
    as [HorderHeadLast HorderLastHead].
  destruct (total_order_T (snd ph) (snd pl)) as [[Hlt | Heq] | Hgt].
  - pose proof (shift_preserves_strict_vertical_order
                  h ph pl
                  (classify l sub r (init (hd_segment (l ++ sub ++ r))))
                  (classify l sub r (term (last_segment (l ++ sub ++ r))))
                  (proj1 Hh) Hlt (HorderHeadLast Hlt)) as Hshifted.
    rewrite <- HshiftHead, <- HshiftLast in Hshifted. lra.
  - apply Hneq. destruct ph as [xh yh], pl as [xl yl].
    simpl in Hx, Heq |- *. f_equal; lra.
  - pose proof (shift_preserves_strict_vertical_order
                  h pl ph
                  (classify l sub r (term (last_segment (l ++ sub ++ r))))
                  (classify l sub r (init (hd_segment (l ++ sub ++ r))))
                  (proj1 Hh) Hgt (HorderLastHead Hgt)) as Hshifted.
    rewrite <- HshiftLast, <- HshiftHead in Hshifted. lra.
Qed.

(* 固定した sub の長方形周りの局所疎性。 *)
Lemma ordinary_sparse_around_prepared :
  forall ds l sub r h,
    PreparedGeometry l sub r ->
    @ClassificationSpec l sub r (classify l sub r) ->
    h_large h sub ->
    height_clears_sub h l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    sparse_around
      (reconnect_segs l sub r h l) sub
      (reconnect_segs l sub r h r).
Proof.
  intros ds l sub r h Hgeometry Hspec Hh Hclear Hsparse Hembed Hext.
  assert (Hne : sub <> []).
  { exact (prepared_sub_nonempty l sub r Hgeometry). }
  assert (Hconn : connected sub).
  { eapply connected_middle.
    exact (embed_listDir_connected ds _ Hembed). }
  assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
  { exact (operate_endpoints_reconnectable_from_spec
             l sub r h Hspec Hh). }
  split.
  - intros p Hextend.
    apply (reconnect_extensions_avoid_sub_rect_from_spec
             l sub r h p Hne Hconn Hspec Hh Hsparse).
    destruct Hextend as [[Hl Hhead] | [Hr Hlast]].
    + left. split.
      * intro Hnil. apply Hl.
        apply length_zero_iff_nil.
        rewrite (reconnect_segs_length l sub r h l).
        now rewrite Hnil.
      * exact Hhead.
    + right. split.
      * intro Hnil. apply Hr.
        apply length_zero_iff_nil.
        rewrite (reconnect_segs_length l sub r h r).
        now rewrite Hnil.
      * exact Hlast.
  - intros s' p Hs' Hp.
    unfold reconnect_segs in Hs'.
    rewrite nonadjacent_sides_map in Hs'.
    apply in_map_iff in Hs'.
    destruct Hs' as [s [Heq Hs]]. subst s'.
    apply (separated_endpoint_box_avoids_sub sub
             (reconnect_one l sub r h s) p Hne).
    + rewrite (reconnect_one_init _ _ _ _ _
                 (Hrec s (nonadjacent_sides_in_whole l sub r s Hs))).
      rewrite (reconnect_one_term _ _ _ _ _
                 (Hrec s (nonadjacent_sides_in_whole l sub r s Hs))).
      exact (operated_nonadjacent_endpoints_separated_from_spec
               l sub r h s Hclear Hspec Hs).
    + exact (proj1 Hp).
Qed.


(* sub の全体包含から、各セグメントの閉三角形の包含も得る。 *)
Lemma contained_sub_triangle : forall sub s p,
  sub_contained_in_endpoint_rect sub ->
  In s sub -> in_segment_triangle s p ->
  in_rect_or_endpoints_at sub p.
Proof.
  intros sub s p Hcontained Hs [[Hpx Hpy] Htriangle].
  pose proof (Hcontained (init s) (ex_intro _ s (conj Hs (onInit s))))
    as [[Hix0 Hix1] [Hiy0 Hiy1]].
  pose proof (Hcontained (term s) (ex_intro _ s (conj Hs (onTerm s))))
    as [[Htx0 Htx1] [Hty0 Hty1]].
  unfold in_rect_or_endpoints_at, in_closed_rect.
  unfold rect_of in Hpx, Hpy; simpl in Hpx, Hpy.
  change (last_segment [s]) with s in Hpx, Hpy.
  unfold Rmin, Rmax in Hpx, Hpy.
  repeat destruct Rle_dec; split; split; lra.
Qed.

(* sub 上のセグメントの端点は固定されるため、引き戻した三角形点も動かない。 *)
Lemma reconnected_sub_triangle_preimage : forall l sub r h i s s' z,
  @EndpointMovementSpec l sub r (classify l sub r) ->
  h_large h sub ->
  nth_error (l ++ sub ++ r) i = Some s ->
  nth_error (reconnect_whole l sub r h) i = Some s' ->
  In s sub ->
  in_segment_triangle s' z -> in_segment_triangle s z.
Proof.
  intros l sub r h i s s' z Hspec Hh Hold Hnew Hin Hz.
  destruct (reconnected_triangle_preimage l sub r h i s s' z
    Hspec Hh Hold Hnew Hz) as [u [Hu [Hx Hy]]].
  rewrite (classified_sub_fixed l sub r Hspec (init s)
    (ex_intro _ s (conj Hin (onInit s)))) in Hy.
  rewrite (classified_sub_fixed l sub r Hspec (term s)
    (ex_intro _ s (conj Hin (onTerm s)))) in Hy.
  unfold region_delta in Hy. rewrite Rmin_left, Rmax_left in Hy by lra.
  assert (z = u) by (destruct z, u; simpl in *; f_equal; lra).
  now subst z.
Qed.

(* 左隣接セグメントは、共有端点の外側の軸に残る。非隣接の sub 部分とは分離する。 *)
Lemma incoming_reconnected_boundary_avoids_inner_sub :
  forall ds l sub r h k t z,
    PreparedGeometry l sub r ->
    @EndpointMovementSpec l sub r (classify l sub r) ->
    h_large h sub ->
    embed_listDir ds (l ++ sub ++ r) ->
    l <> [] ->
    nth_error sub k = Some t -> (0 < k)%nat ->
    in_segment_rect_or_endpoints (reconnect_one l sub r h (last_segment l)) z ->
    in_segment_rect_or_endpoints t z -> False.
Proof.
  intros ds l sub r h k t z Hgeom Hspec Hh Hembed Hl Ht Hk Hz Hzt.
  assert (Hne : sub <> []) by exact (prepared_sub_nonempty l sub r Hgeom).
  assert (Hlen : (1 < length sub)%nat).
  { apply nth_error_lt in Ht. lia. }
  assert (Hlast : nth_error (l ++ sub ++ r) (length l - 1) =
                   Some (last_segment l)).
  { rewrite nth_error_app1 by (destruct l; simpl in *; [contradiction | lia]).
    now apply nth_error_last. }
  assert (Hfirst : nth_error (l ++ sub ++ r) (S (length l - 1)) =
                    Some (hd_segment sub)).
  { replace (S (length l - 1)) with (length l) by
      (destruct l; simpl in *; [contradiction | lia]).
    rewrite nth_error_app2 by lia.
    replace (length l - length l)%nat with 0%nat by lia.
    destruct sub; [contradiction | reflexivity]. }
  destruct Hembed as [sc [Hds Hembed]].
  destruct (embed_scurve_adjacent_data sc (l ++ sub ++ r) _
    (last_segment l) (hd_segment sub) Hembed Hlast Hfirst)
    as [pa [pb [Ha [Hb [Hdc Hjoin]]]]].
  assert (Hin : In (last_segment l) (l ++ sub ++ r)).
  { apply in_or_app. left. now apply last_In. }
  pose proof (operate_endpoints_reconnectable_from_spec l sub r h Hspec Hh
    (last_segment l) Hin) as Hrec.
  destruct (reconnect_one_endpoints_orn l sub r h (last_segment l) Hrec)
    as [Hi [Ht' Ho]].
  assert (Hfixed : operate_point l sub r h (term (last_segment l)) =
                   init (hd_segment sub)).
  { rewrite Hjoin. unfold ReconnectByClassifier.operate_point.
    rewrite (classified_sub_fixed l sub r Hspec (init (hd_segment sub))).
    - reflexivity.
    - exists (hd_segment sub). split; [destruct sub; [contradiction | now left] | apply onInit]. }
  rewrite Hfixed in Ht'.
  destruct (first_sub_segment_axis_order sub Hlen
    (prepared_sub_strictly_inside l sub r Hgeom)
    (prepared_sub_x_order l sub r Hgeom)) as [HfirstX [HfirstUp HfirstDown]].
  pose proof (sub_endpoint_y_distinct sub Hlen
    (prepared_sub_strictly_inside l sub r Hgeom)) as Hdistinct.
  destruct (operated_segment_axis_orders_from_spec l sub r h
    (last_segment l) Hspec (proj1 Hh) Hin) as [HaxesX HaxesY].
  destruct (incoming_east_segment_axis_separation
    (last_segment l) (hd_segment sub) pa pb Ha Hb Hdc HfirstX)
    as [Hleft | [[Hnorth HfirstNorth] | [Hsouth HfirstSouth]]].
  - pose proof (prepared_inner_segment_left_x l sub r k t Hgeom Ht Hk) as Hinner.
    assert (Hx : fst (init (reconnect_one l sub r h (last_segment l))) <
                 fst (term (reconnect_one l sub r h (last_segment l)))).
    { rewrite Hi, Ht', operate_point_fst.
      unfold init_x, term_x in Hleft. rewrite Hjoin in Hleft.
      exact Hleft. }
    change ((Rmin (fst (init (reconnect_one l sub r h (last_segment l)))) (fst (term (reconnect_one l sub r h (last_segment l)))) <= fst z <=
             Rmax (fst (init (reconnect_one l sub r h (last_segment l)))) (fst (term (reconnect_one l sub r h (last_segment l))))) /\
            (Rmin (snd (init (reconnect_one l sub r h (last_segment l)))) (snd (term (reconnect_one l sub r h (last_segment l)))) <= snd z <=
             Rmax (snd (init (reconnect_one l sub r h (last_segment l)))) (snd (term (reconnect_one l sub r h (last_segment l)))))) in Hz.
    destruct Hz as [Hzx Hzy]. rewrite Rmax_right in Hzx by exact (Rlt_le _ _ Hx).
    rewrite Ht' in Hzx.
    destruct Hzt as [[Htxlo Htxhi] [Htylo Htyhi]].
    pose proof (prepared_sub_x_order l sub r Hgeom).
    change (Rmin (fst (init (hd_segment sub)))
      (fst (term (last_segment sub))) < rx0 (rect_of [t])) in Hinner.
    rewrite Rmin_left in Hinner by lra.
    lra.
  - assert (Hglobal : snd (init (hd_segment sub)) <
                      snd (term (last_segment sub))).
    { destruct (Rlt_dec (snd (init (hd_segment sub)))
                       (snd (term (last_segment sub)))); [assumption |].
      assert (Hdown : snd (term (last_segment sub)) <
                      snd (init (hd_segment sub))) by lra.
      specialize (HfirstDown Hdown). unfold init_y, term_y in *. lra. }
    pose proof (proj1 (inner_segment_left_y sub k t Hne
      (prepared_sub_strictly_inside l sub r Hgeom) Ht Hk) Hglobal) as Hinner.
    assert (Hy : snd (init (reconnect_one l sub r h (last_segment l))) <
                 snd (term (reconnect_one l sub r h (last_segment l)))).
    { rewrite Hi, Ht', <- Hfixed. apply (proj1 HaxesY Hnorth). }
    change ((Rmin (fst (init (reconnect_one l sub r h (last_segment l)))) (fst (term (reconnect_one l sub r h (last_segment l)))) <= fst z <=
             Rmax (fst (init (reconnect_one l sub r h (last_segment l)))) (fst (term (reconnect_one l sub r h (last_segment l))))) /\
            (Rmin (snd (init (reconnect_one l sub r h (last_segment l)))) (snd (term (reconnect_one l sub r h (last_segment l)))) <= snd z <=
             Rmax (snd (init (reconnect_one l sub r h (last_segment l)))) (snd (term (reconnect_one l sub r h (last_segment l)))))) in Hz.
    destruct Hz as [Hzx Hzy]. rewrite Rmax_right in Hzy by exact (Rlt_le _ _ Hy).
    rewrite Ht' in Hzy.
    destruct Hzt as [[Htxlo Htxhi] [Htylo Htyhi]]. lra.
  - assert (Hglobal : snd (term (last_segment sub)) <
                      snd (init (hd_segment sub))).
    { destruct (Rlt_dec (snd (term (last_segment sub)))
                       (snd (init (hd_segment sub)))); [assumption |].
      assert (Hup : snd (init (hd_segment sub)) <
                    snd (term (last_segment sub))) by lra.
      specialize (HfirstUp Hup). unfold init_y, term_y in *. lra. }
    pose proof (proj2 (inner_segment_left_y sub k t Hne
      (prepared_sub_strictly_inside l sub r Hgeom) Ht Hk) Hglobal) as Hinner.
    assert (Hy : snd (term (reconnect_one l sub r h (last_segment l))) <
                 snd (init (reconnect_one l sub r h (last_segment l)))).
    { pose proof (proj2 (classified_segment_endpoints_monotone
        l sub r Hspec (last_segment l) Hin) Hsouth) as Hregions.
      rewrite Hi, Ht', <- Hfixed.
      unfold ReconnectByClassifier.operate_point.
      exact (shift_preserves_strict_vertical_order h
        (term (last_segment l)) (init (last_segment l)) _ _
        (proj1 Hh) Hsouth Hregions). }
    change ((Rmin (fst (init (reconnect_one l sub r h (last_segment l)))) (fst (term (reconnect_one l sub r h (last_segment l)))) <= fst z <=
             Rmax (fst (init (reconnect_one l sub r h (last_segment l)))) (fst (term (reconnect_one l sub r h (last_segment l))))) /\
            (Rmin (snd (init (reconnect_one l sub r h (last_segment l)))) (snd (term (reconnect_one l sub r h (last_segment l)))) <= snd z <=
             Rmax (snd (init (reconnect_one l sub r h (last_segment l)))) (snd (term (reconnect_one l sub r h (last_segment l)))))) in Hz.
    destruct Hz as [Hzx Hzy]. rewrite Rmin_right in Hzy by exact (Rlt_le _ _ Hy).
    rewrite Ht' in Hzy.
    destruct Hzt as [[Htxlo Htxhi] [Htylo Htyhi]]. lra.
Qed.


(* 右隣接セグメントについても、共有端点より内側へ戻らない軸を使う。 *)
Lemma outgoing_reconnected_boundary_avoids_inner_sub :
  forall ds l sub r h k t z,
    PreparedGeometry l sub r ->
    @EndpointMovementSpec l sub r (classify l sub r) ->
    h_large h sub ->
    embed_listDir ds (l ++ sub ++ r) ->
    r <> [] ->
    nth_error sub k = Some t -> (S k < length sub)%nat ->
    in_segment_rect_or_endpoints (reconnect_one l sub r h (hd_segment r)) z ->
    in_segment_rect_or_endpoints t z -> False.
Proof.
  intros ds l sub r h k t z Hgeom Hspec Hh Hembed Hr Ht Hk Hz Hzt.
  assert (Hne : sub <> []) by exact (prepared_sub_nonempty l sub r Hgeom).
  assert (Hlen : (1 < length sub)%nat) by lia.
  assert (Hlast : nth_error (l ++ sub ++ r) (length l + (length sub - 1)) =
                   Some (last_segment sub)).
  { rewrite nth_error_app2 by lia.
    replace (length l + (length sub - 1) - length l)%nat
      with (length sub - 1)%nat by lia.
    rewrite nth_error_app1 by lia. now apply nth_error_last. }
  assert (Hfirst : nth_error (l ++ sub ++ r) (S (length l + (length sub - 1))) =
                    Some (hd_segment r)).
  { replace (S (length l + (length sub - 1))) with (length l + length sub)%nat by lia.
    rewrite nth_error_app2 by lia.
    replace (length l + length sub - length l)%nat with (length sub) by lia.
    rewrite nth_error_app2 by lia.
    replace (length sub - length sub)%nat with 0%nat by lia.
    destruct r; [contradiction | reflexivity]. }
  destruct Hembed as [sc [Hds Hembed]].
  destruct (embed_scurve_adjacent_data sc (l ++ sub ++ r) _
    (last_segment sub) (hd_segment r) Hembed Hlast Hfirst)
    as [pa [pb [Ha [Hb [Hdc Hjoin]]]]].
  assert (Hin : In (hd_segment r) (l ++ sub ++ r)).
  { apply in_or_app. right. apply in_or_app. right.
    destruct r; [contradiction | now left]. }
  pose proof (operate_endpoints_reconnectable_from_spec l sub r h Hspec Hh
    (hd_segment r) Hin) as Hrec.
  destruct (reconnect_one_endpoints_orn l sub r h (hd_segment r) Hrec)
    as [Hi [Ht' Ho]].
  assert (Hfixed : operate_point l sub r h (init (hd_segment r)) =
                   term (last_segment sub)).
  { rewrite <- Hjoin. unfold ReconnectByClassifier.operate_point.
    rewrite (classified_sub_fixed l sub r Hspec (term (last_segment sub))).
    - reflexivity.
    - exists (last_segment sub). split; [now apply last_In | apply onTerm]. }
  rewrite Hfixed in Hi.
  destruct (last_sub_segment_axis_order sub Hlen
    (prepared_sub_strictly_inside l sub r Hgeom)
    (prepared_sub_x_order l sub r Hgeom)) as [HlastX [HlastUp HlastDown]].
  pose proof (sub_endpoint_y_distinct sub Hlen
    (prepared_sub_strictly_inside l sub r Hgeom)) as Hdistinct.
  destruct (operated_segment_axis_orders_from_spec l sub r h
    (hd_segment r) Hspec (proj1 Hh) Hin) as [HaxesX HaxesY].
  destruct (outgoing_east_segment_axis_separation
    (last_segment sub) (hd_segment r) pa pb Ha Hb Hdc HlastX)
    as [Hright | [[HlastNorth Hnorth] | [HlastSouth Hsouth]]].
  - pose proof (prepared_inner_segment_right_x l sub r k t Hgeom Ht Hk) as Hinner.
    assert (Hx : fst (init (reconnect_one l sub r h (hd_segment r))) <
                 fst (term (reconnect_one l sub r h (hd_segment r)))).
    { rewrite Hi, Ht', operate_point_fst.
      unfold init_x, term_x in Hright. rewrite <- Hjoin in Hright.
      exact Hright. }
    change ((Rmin (fst (init (reconnect_one l sub r h (hd_segment r)))) (fst (term (reconnect_one l sub r h (hd_segment r)))) <= fst z <=
             Rmax (fst (init (reconnect_one l sub r h (hd_segment r)))) (fst (term (reconnect_one l sub r h (hd_segment r))))) /\
            (Rmin (snd (init (reconnect_one l sub r h (hd_segment r)))) (snd (term (reconnect_one l sub r h (hd_segment r)))) <= snd z <=
             Rmax (snd (init (reconnect_one l sub r h (hd_segment r)))) (snd (term (reconnect_one l sub r h (hd_segment r)))))) in Hz.
    destruct Hz as [Hzx Hzy]. rewrite Rmin_left in Hzx by exact (Rlt_le _ _ Hx).
    rewrite Hi in Hzx.
    destruct Hzt as [[Htxlo Htxhi] [Htylo Htyhi]].
    pose proof (prepared_sub_x_order l sub r Hgeom).
    change (rx1 (rect_of [t]) < Rmax (fst (init (hd_segment sub)))
      (fst (term (last_segment sub)))) in Hinner.
    rewrite Rmax_right in Hinner by lra.
    lra.
  - assert (Hglobal : snd (init (hd_segment sub)) <
                      snd (term (last_segment sub))).
    { destruct (Rlt_dec (snd (init (hd_segment sub)))
                       (snd (term (last_segment sub)))); [assumption |].
      assert (Hdown : snd (term (last_segment sub)) <
                      snd (init (hd_segment sub))) by lra.
      specialize (HlastDown Hdown). unfold init_y, term_y in *. lra. }
    pose proof (proj1 (inner_segment_right_y sub k t Hne
      (prepared_sub_strictly_inside l sub r Hgeom) Ht Hk) Hglobal) as Hinner.
    assert (Hy : snd (init (reconnect_one l sub r h (hd_segment r))) <
                 snd (term (reconnect_one l sub r h (hd_segment r)))).
    { rewrite Hi, Ht', <- Hfixed. apply (proj1 HaxesY Hnorth). }
    change ((Rmin (fst (init (reconnect_one l sub r h (hd_segment r)))) (fst (term (reconnect_one l sub r h (hd_segment r)))) <= fst z <=
             Rmax (fst (init (reconnect_one l sub r h (hd_segment r)))) (fst (term (reconnect_one l sub r h (hd_segment r))))) /\
            (Rmin (snd (init (reconnect_one l sub r h (hd_segment r)))) (snd (term (reconnect_one l sub r h (hd_segment r)))) <= snd z <=
             Rmax (snd (init (reconnect_one l sub r h (hd_segment r)))) (snd (term (reconnect_one l sub r h (hd_segment r)))))) in Hz.
    destruct Hz as [Hzx Hzy]. rewrite Rmin_left in Hzy by exact (Rlt_le _ _ Hy).
    rewrite Hi in Hzy.
    destruct Hzt as [[Htxlo Htxhi] [Htylo Htyhi]]. lra.
  - assert (Hglobal : snd (term (last_segment sub)) <
                      snd (init (hd_segment sub))).
    { destruct (Rlt_dec (snd (term (last_segment sub)))
                       (snd (init (hd_segment sub)))); [assumption |].
      assert (Hup : snd (init (hd_segment sub)) <
                    snd (term (last_segment sub))) by lra.
      specialize (HlastUp Hup). unfold init_y, term_y in *. lra. }
    pose proof (proj2 (inner_segment_right_y sub k t Hne
      (prepared_sub_strictly_inside l sub r Hgeom) Ht Hk) Hglobal) as Hinner.
    assert (Hy : snd (term (reconnect_one l sub r h (hd_segment r))) <
                 snd (init (reconnect_one l sub r h (hd_segment r)))).
    { pose proof (proj2 (classified_segment_endpoints_monotone
        l sub r Hspec (hd_segment r) Hin) Hsouth) as Hregions.
      rewrite Hi, Ht', <- Hfixed.
      unfold ReconnectByClassifier.operate_point.
      exact (shift_preserves_strict_vertical_order h
        (term (hd_segment r)) (init (hd_segment r)) _ _
        (proj1 Hh) Hsouth Hregions). }
    change ((Rmin (fst (init (reconnect_one l sub r h (hd_segment r)))) (fst (term (reconnect_one l sub r h (hd_segment r)))) <= fst z <=
             Rmax (fst (init (reconnect_one l sub r h (hd_segment r)))) (fst (term (reconnect_one l sub r h (hd_segment r))))) /\
            (Rmin (snd (init (reconnect_one l sub r h (hd_segment r)))) (snd (term (reconnect_one l sub r h (hd_segment r)))) <= snd z <=
             Rmax (snd (init (reconnect_one l sub r h (hd_segment r)))) (snd (term (reconnect_one l sub r h (hd_segment r)))))) in Hz.
    destruct Hz as [Hzx Hzy]. rewrite Rmax_left in Hzy by exact (Rlt_le _ _ Hy).
    rewrite Hi in Hzy.
    destruct Hzt as [[Htxlo Htxhi] [Htylo Htyhi]]. lra.
Qed.


(* 三分割列の出現位置を、添字を保ったまま一意な部分へ分ける。 *)
Lemma nth_error_app_three : forall (a b c : list Segment) i s,
  nth_error (a ++ b ++ c) i = Some s ->
  ((i < length a)%nat /\ nth_error a i = Some s)
  \/ ((length a <= i < length a + length b)%nat /\
      nth_error b (i - length a) = Some s)
  \/ ((length a + length b <= i)%nat /\
      nth_error c (i - length a - length b) = Some s).
Proof.
  intros a b c i s H.
  destruct (Nat.lt_ge_cases i (length a)) as [Ha | Ha].
  - left. split; [exact Ha |]. now rewrite nth_error_app1 in H.
  - rewrite nth_error_app2 in H by lia.
    destruct (Nat.lt_ge_cases (i - length a) (length b)) as [Hb | Hb].
    + right; left. split; [lia |]. now rewrite nth_error_app1 in H.
    + right; right. split; [lia |]. now rewrite nth_error_app2 in H by lia.
Qed.

(* 元の三角形疎性で比較点を本体へ移し、分類仕様から変位区間の順序を得る。 *)
Lemma classified_external_triangle_delta_order :
  forall l sub r h i j s t u v,
    @ClassificationSpec l sub r (classify l sub r) ->
    sparse_embedding (l ++ sub ++ r) ->
    0 <= h ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (l ++ sub ++ r) j = Some t ->
    (S i < j \/ S j < i)%nat ->
    In s (l ++ r) -> In t (l ++ r) ->
    in_segment_triangle s u -> in_segment_triangle t v ->
    fst u = fst v -> snd u < snd v ->
    Rmax (region_delta h (classify l sub r (init s)))
         (region_delta h (classify l sub r (term s))) <=
    Rmin (region_delta h (classify l sub r (init t)))
         (region_delta h (classify l sub r (term t))).
Proof.
  intros l sub r h i j s t u v Hspec Hsparse Hh Hs Ht Hfar Hsin Htin Hu Hv Hx Hy.
  destruct (nth_error_far_in_nonadjacent_sides
    (l ++ sub ++ r) i j s t Hs Ht Hfar) as [lo [ro [Hsplit Hin]]].
  assert (Hdisjoint : forall p,
    in_segment_triangle s p -> ~ in_segment_triangle t p).
  { intros p Hsp Htp. exact ((proj2 (Hsparse lo s ro Hsplit)) t p Hin Htp Hsp). }
  destruct (disjoint_triangle_order_has_segment_witnesses s t u v
    Hdisjoint Hu Hv Hx Hy) as [a [b [Ha [Hb [Habx Haby]]]]].
  apply Rmax_lub; apply Rmin_glb; apply region_delta_order; try exact Hh;
    eapply (classified_external_segment_order l sub r Hspec
      i j s t _ _ a b); try eassumption; unfold endpoint_of_seg; auto.
Qed.

(* 外側の二三角形を同じ x へ引き戻し、旧分離と変位区間の順序から交差を排除する。 *)
Lemma reconnected_external_triangles_disjoint :
  forall l sub r h i j s t s' t' z,
    @ClassificationSpec l sub r (classify l sub r) ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (l ++ sub ++ r) j = Some t ->
    nth_error (reconnect_whole l sub r h) i = Some s' ->
    nth_error (reconnect_whole l sub r h) j = Some t' ->
    (S i < j \/ S j < i)%nat ->
    In s (l ++ r) -> In t (l ++ r) ->
    in_segment_triangle s' z -> in_segment_triangle t' z -> False.
Proof.
  intros l sub r h i j s t s' t' z Hspec Hh Hsparse
    Hs Ht HnewS HnewT Hfar Hsin Htin HzS HzT.
  destruct (reconnected_triangle_preimage
    l sub r h i s s' z Hspec Hh Hs HnewS HzS) as [u [Hu [Hux Hus]]].
  destruct (reconnected_triangle_preimage
    l sub r h j t t' z Hspec Hh Ht HnewT HzT) as [v [Hv [Hvx Hvs]]].
  assert (Hneq : snd u <> snd v).
  { intros Hy. assert (Heq : u = v).
    { destruct u, v; simpl in *; f_equal; lra. }
    destruct (nth_error_far_in_nonadjacent_sides
      (l ++ sub ++ r) i j s t Hs Ht Hfar) as [lo [ro [Hsplit Hin]]].
    subst v. exact ((proj2 (Hsparse lo s ro Hsplit)) t u Hin Hv Hu). }
  destruct (Rlt_dec (snd u) (snd v)) as [Huv | Huv].
  - pose proof (classified_external_triangle_delta_order l sub r h
      i j s t u v Hspec Hsparse (Rlt_le _ _ (proj1 Hh)) Hs Ht Hfar Hsin Htin Hu Hv
      ltac:(congruence) Huv) as Horder.
    unfold Rmin, Rmax in *. repeat destruct Rle_dec; lra.
  - assert (Hvu : snd v < snd u) by lra.
    pose proof (classified_external_triangle_delta_order l sub r h
      j i t s v u Hspec Hsparse (Rlt_le _ _ (proj1 Hh)) Ht Hs ltac:(lia)
      Htin Hsin Hv Hu ltac:(congruence) Hvu) as Horder.
    unfold Rmin, Rmax in *. repeat destruct Rle_dec; lra.
Qed.

(* 再接続される外側出現は、その部分列を map した同じ位置にある。 *)
Lemma reconnect_whole_nth_outside : forall l sub r h i s s',
  nth_error (l ++ sub ++ r) i = Some s ->
  nth_error (reconnect_whole l sub r h) i = Some s' ->
  ((i < length l)%nat \/ (length l + length sub <= i)%nat) ->
  s' = reconnect_one l sub r h s.
Proof.
  intros l sub r h i s s' Hold Hnew Houtside.
  unfold ReconnectByClassifier.reconnect_whole in Hnew.
  unfold ReconnectByClassifier.reconnect_segs in Hnew.
  destruct Houtside as [Hl | Hr].
  - rewrite nth_error_app1 in Hold by exact Hl.
    rewrite nth_error_app1 in Hnew by (rewrite length_map; exact Hl).
    rewrite nth_error_map, Hold in Hnew. now inversion Hnew.
  - rewrite nth_error_app2 in Hold by lia.
    rewrite nth_error_app2 in Hold by lia.
    rewrite nth_error_app2 in Hnew by (rewrite length_map; lia).
    rewrite length_map in Hnew.
    rewrite nth_error_app2 in Hnew by lia.
    rewrite nth_error_map, Hold in Hnew. now inversion Hnew.
Qed.

(* 非隣接の外側では、再接続後の閉長方形ごと sub 長方形から離れる。 *)
Lemma reconnected_far_triangle_avoids_sub_rect :
  forall l sub r h i s s' z,
    sub <> [] ->
    @ClassificationSpec l sub r (classify l sub r) ->
    h_large h sub -> height_clears_sub h l sub r ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (reconnect_whole l sub r h) i = Some s' ->
    In s (nonadjacent_sides l r) ->
    in_segment_triangle s' z -> ~ in_rect_or_endpoints_at sub z.
Proof.
  intros l sub r h i s s' z Hne Hspec Hh Hclear Hold Hnew Hin Hz.
  assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
  { exact (operate_endpoints_reconnectable_from_spec l sub r h Hspec Hh). }
  destruct (reconnect_whole_nth_spec l sub r h i s s' Hspec Hrec Hold Hnew)
    as [Ho [Hi Ht]].
  assert (Hsep : endpoint_box_separated_from_sub sub (init s') (term s')).
  { rewrite Hi, Ht. exact (operated_nonadjacent_endpoints_separated_from_spec
      l sub r h s Hclear Hspec Hin). }
  apply (separated_endpoint_box_avoids_sub sub s' z).
  - exact Hne.
  - exact Hsep.
  - exact (proj1 Hz).
Qed.


Lemma nth_before_last_in_removelast : forall (xs : list Segment) i s,
  nth_error xs i = Some s -> (S i < length xs)%nat ->
  In s (removelast xs).
Proof.
  induction xs as [|a xs IH]; intros i s Hnth Hlt;
    [destruct i; discriminate |].
  destruct xs as [|b xs]; [simpl in Hlt; lia |].
  destruct i as [|i].
  - simpl in Hnth. inversion Hnth; subst. now left.
  - simpl in Hnth, Hlt. right. eapply IH; eauto; simpl; lia.
Qed.

Lemma nth_sub_or_sides : forall (l sub r : list Segment) i s,
  nth_error (l ++ sub ++ r) i = Some s ->
  (exists k, i = (length l + k)%nat /\ nth_error sub k = Some s)
  \/ (((i < length l)%nat \/ (length l + length sub <= i)%nat) /\ In s (l ++ r)).
Proof.
  intros l sub r i s Hnth.
  destruct (nth_error_app_three l sub r i s Hnth)
    as [[Hi Hs] | [[Hi Hs] | [Hi Hs]]].
  - right. split; [now left | apply in_or_app; left; now apply nth_error_In in Hs].
  - left. exists (i - length l)%nat. split; [lia | exact Hs].
  - right. split; [now right | apply in_or_app; right; now apply nth_error_In in Hs].
Qed.

(* sub と外側の比較は、遠いセグメントの長方形退避と二つの隣接境界に分かれる。 *)
Lemma reconnected_side_triangle_avoids_sub_triangle :
  forall ds l sub r h i k s t s' z,
    PreparedGeometry l sub r ->
    @ClassificationSpec l sub r (classify l sub r) ->
    h_large h sub -> height_clears_sub h l sub r ->
    embed_listDir ds (l ++ sub ++ r) ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (reconnect_whole l sub r h) i = Some s' ->
    nth_error sub k = Some t ->
    (S i < length l + k \/ S (length l + k) < i)%nat ->
    ((i < length l)%nat \/ (length l + length sub <= i)%nat) ->
    in_segment_triangle s' z -> in_segment_triangle t z -> False.
Proof.
  intros ds l sub r h i k s t s' z Hgeom Hspec Hh Hclear Hembed
    Hold Hnew Ht Hfar Houtside Hz Hzt.
  assert (Hkt : (k < length sub)%nat) by (eapply nth_error_lt; eassumption).
  pose proof (prepared_sub_nonempty l sub r Hgeom) as Hne.
  assert (Hsubz : in_rect_or_endpoints_at sub z).
  { exact (contained_sub_triangle sub t z
      (prepared_sub_contained l sub r Hgeom) (nth_error_In _ _ Ht) Hzt). }
  pose proof (reconnect_whole_nth_outside l sub r h i s s' Hold Hnew Houtside)
    as Hvalue.
  destruct Houtside as [Hleft | Hright].
  - assert (Hlocal : nth_error l i = Some s).
    { now rewrite nth_error_app1 in Hold. }
    destruct (Nat.lt_ge_cases (S i) (length l)) as [Hinterior | Hboundary].
    + assert (Hin : In s (nonadjacent_sides l r)).
      { unfold nonadjacent_sides. apply in_or_app. left.
        eapply nth_before_last_in_removelast; eassumption. }
      exact (reconnected_far_triangle_avoids_sub_rect l sub r h i s s' z
        Hne Hspec Hh Hclear Hold Hnew Hin Hz Hsubz).
    + assert (Hl : l <> []) by (destruct l; simpl in *; [lia | discriminate]).
      assert (Hi : i = (length l - 1)%nat) by lia.
      assert (Hs : s = last_segment l).
      { pose proof (@nth_error_last Segment l default_segment Hl) as Hlast.
        rewrite <- Hi in Hlast. rewrite Hlocal in Hlast. now inversion Hlast. }
      assert (Hk : (0 < k)%nat) by lia.
      rewrite Hvalue, Hs in Hz.
      exact (incoming_reconnected_boundary_avoids_inner_sub
        ds l sub r h k t z Hgeom Hspec Hh Hembed Hl Ht Hk (proj1 Hz) (proj1 Hzt)).
  - assert (Hlocal : nth_error r (i - length l - length sub) = Some s).
    { rewrite nth_error_app2 in Hold by lia.
      now rewrite nth_error_app2 in Hold by lia. }
    destruct (Nat.eq_dec (i - length l - length sub) 0) as [Hboundary | Hinterior].
    + assert (Hr : r <> []).
      { intros ->. rewrite Hboundary in Hlocal. discriminate. }
      assert (Hs : s = hd_segment r).
      { rewrite Hboundary in Hlocal.
        destruct r; [discriminate | simpl in Hlocal; now inversion Hlocal]. }
      assert (Hk : (S k < length sub)%nat) by lia.
      rewrite Hvalue, Hs in Hz.
      exact (outgoing_reconnected_boundary_avoids_inner_sub
        ds l sub r h k t z Hgeom Hspec Hh Hembed Hr Ht Hk (proj1 Hz) (proj1 Hzt)).
    + assert (Hin : In s (nonadjacent_sides l r)).
      { unfold nonadjacent_sides. apply in_or_app. right.
        destruct r as [|a tail];
          [destruct (i - length l - length sub)%nat; discriminate |].
        destruct (i - length l - length sub)%nat as [|j] eqn:Hindex;
          [contradiction |].
        simpl in Hlocal. now apply nth_error_In in Hlocal. }
      exact (reconnected_far_triangle_avoids_sub_rect l sub r h i s s' z
        Hne Hspec Hh Hclear Hold Hnew Hin Hz Hsubz).
Qed.

(* sub との順序反転を許しつつ、固定部分・隣接境界・外側対を別々に分離する。 *)
Lemma reconnect_preserves_triangle_separation_from_prepared_spec :
  forall ds l sub r h,
    PreparedGeometry l sub r ->
    @ClassificationSpec l sub r (classify l sub r) ->
    h_large h sub -> height_clears_sub h l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    segment_triangles_separated (reconnect_whole l sub r h).
Proof.
  intros ds l sub r h Hgeom Hspec Hh Hclear Hsparse Hembed
    ls s' rs Hsplit t' z Hin HzT HzS.
  destruct (split_nonadjacent_nth_errors
    (reconnect_whole l sub r h) ls s' rs t' Hsplit Hin)
    as [i [j [HnewS [HnewT Hfar]]]].
  assert (Hlen : length (l ++ sub ++ r) = length (reconnect_whole l sub r h)).
  { symmetry. apply reconnect_whole_length. }
  destruct (nth_error_exists_at_equal_length _ _ i s' Hlen HnewS) as [s Hs].
  destruct (nth_error_exists_at_equal_length _ _ j t' Hlen HnewT) as [t Ht].
  destruct (nth_sub_or_sides l sub r i s Hs) as [[ks [Hi HsubS]] | [Hi HsideS]];
    destruct (nth_sub_or_sides l sub r j t Ht) as [[kt [Hj HsubT]] | [Hj HsideT]].
  - pose proof (reconnected_sub_triangle_preimage l sub r h i s s' z
      Hspec Hh Hs HnewS (nth_error_In _ _ HsubS) HzS) as Hu.
    pose proof (reconnected_sub_triangle_preimage l sub r h j t t' z
      Hspec Hh Ht HnewT (nth_error_In _ _ HsubT) HzT) as Hv.
    destruct (nth_error_far_in_nonadjacent_sides
      (l ++ sub ++ r) i j s t Hs Ht Hfar) as [lo [ro [HsplitOld Htin]]].
    exact ((proj2 (Hsparse lo s ro HsplitOld)) t z Htin Hv Hu).
  - pose proof (reconnected_sub_triangle_preimage l sub r h i s s' z
      Hspec Hh Hs HnewS (nth_error_In _ _ HsubS) HzS) as Hu.
    exact (reconnected_side_triangle_avoids_sub_triangle ds l sub r h
      j ks t s t' z Hgeom Hspec Hh Hclear Hembed Ht HnewT HsubS
      ltac:(lia) Hj HzT Hu).
  - pose proof (reconnected_sub_triangle_preimage l sub r h j t t' z
      Hspec Hh Ht HnewT (nth_error_In _ _ HsubT) HzT) as Hv.
    exact (reconnected_side_triangle_avoids_sub_triangle ds l sub r h
      i kt s t s' z Hgeom Hspec Hh Hclear Hembed Hs HnewS HsubT
      ltac:(lia) Hi HzS Hv).
  - exact (reconnected_external_triangles_disjoint l sub r h
      i j s t s' t' z Hspec Hh Hsparse Hs Ht HnewS HnewT Hfar
      HsideS HsideT HzS HzT).
Qed.

(* 外側には順序保存、固定した sub には長方形退避を使う。 *)
Lemma reconnect_preserves_triangle_extension_avoidance_from_prepared_spec :
  forall ds l sub r h,
    PreparedGeometry l sub r ->
    @ClassificationSpec l sub r (classify l sub r) ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    extensions_avoid_segment_triangles (reconnect_whole l sub r h).
Proof.
  intros ds l sub r h Hgeom Hspec Hh Hsparse Hembed Hext
    ls s' rs Hsplit p Hextend.
  pose proof (prepared_sub_nonempty l sub r Hgeom) as Hne.
  assert (Hconn : connected sub).
  { eapply connected_middle. exact (embed_listDir_connected _ _ Hembed). }
  assert (Hnew : nth_error (reconnect_whole l sub r h) (length ls) = Some s').
  { rewrite Hsplit. rewrite nth_error_app2 by lia.
    replace (length ls - length ls)%nat with 0%nat by lia.
    reflexivity. }
  assert (Hlen : length (l ++ sub ++ r) =
                 length (reconnect_whole l sub r h)).
  { symmetry. apply reconnect_whole_length. }
  destruct (nth_error_exists_at_equal_length
              (l ++ sub ++ r) (reconnect_whole l sub r h)
              (length ls) s' Hlen Hnew) as [s Hold].
  destruct (@nth_error_split Segment (l ++ sub ++ r)
              (length ls) s Hold) as [lo [ro [HsplitOld HloLen]]].
  assert (Hin : In s (l ++ sub ++ r)) by now apply nth_error_In in Hold.
  destruct Hextend as [[Hls Hhead] | [Hrs Hlast]].
  - destruct (reconnect_head_strict_extension_preimage_from_spec
                l sub r h p
                Hne
                Hsparse Hspec (Rlt_le _ _ (proj1 Hh)) Hhead)
      as [q [Hq Hshift]].
    assert (Hlo : lo <> []).
    { intros Heq. subst lo. simpl in HloLen.
      destruct ls; [contradiction | simpl in HloLen; lia]. }
    assert (Houtside : ~ in_segment_triangle s q).
    { exact ((proj1 (Hsparse lo s ro HsplitOld)) q
        (or_introl (conj Hlo Hq))). }
    destruct (classic (In s (l ++ r))) as [Hside | Hside].
    + eapply (shifted_point_avoids_reconnected_triangle
        l sub r h (length ls) s s' q p
        (classify l sub r (init (hd_segment (l ++ sub ++ r)))))
        ; try eassumption; try exact (classification_endpoint_spec l sub r Hspec).
      intros e He Hx.
      exact (classified_extension_segment_order_outside_gap
        l sub r Hspec HeadEnd s e q (or_introl Hside) He Hq Hx).
    + assert (Hsub : In s sub).
      { repeat rewrite in_app_iff in Hin.
        rewrite in_app_iff in Hside. tauto. }
      intro Hp.
      pose proof (reconnected_sub_triangle_preimage l sub r h
        (length ls) s s' p Hspec Hh Hold Hnew Hsub Hp) as HsubTriangle.
      destruct (classic (l = [])) as [Hnil | Hnonempty].
      * assert (Hfix : classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegFix).
        {
        subst l. destruct sub as [|a tail]; [contradiction |].
        change (classify [] (a :: tail) r (init a) = RegFix).
        apply (classified_sub_fixed [] (a :: tail) r Hspec).
        apply onSegmentlist_init_hd. discriminate.
        }
        rewrite Hfix in Hshift. simpl in Hshift. subst p.
        exact (Houtside HsubTriangle).
      * apply (reconnect_extensions_avoid_sub_rect_from_spec
          l sub r h p Hne Hconn Hspec Hh Hsparse).
        -- left. split; assumption.
        -- exact (contained_sub_triangle sub s p
             (prepared_sub_contained l sub r Hgeom) Hsub HsubTriangle).
  - destruct (reconnect_last_strict_extension_preimage_from_spec
                l sub r h p
                Hne
                Hsparse Hspec (Rlt_le _ _ (proj1 Hh)) Hlast)
      as [q [Hq Hshift]].
    assert (Hro : ro <> []).
    { intros Heq. subst ro.
      assert (HlengthNew :
        length (reconnect_whole l sub r h) =
        (length ls + 1 + length rs)%nat).
      { rewrite Hsplit. repeat rewrite length_app. simpl. lia. }
      assert (HlengthOld :
        length (l ++ sub ++ r) = (length lo + 1)%nat).
      { rewrite HsplitOld. repeat rewrite length_app. simpl. lia. }
      destruct rs; [contradiction | simpl in *; lia]. }
    assert (Houtside : ~ in_segment_triangle s q).
    { exact ((proj1 (Hsparse lo s ro HsplitOld)) q
        (or_intror (conj Hro Hq))). }
    destruct (classic (In s (l ++ r))) as [Hside | Hside].
    + eapply (shifted_point_avoids_reconnected_triangle
        l sub r h (length ls) s s' q p
        (classify l sub r (term (last_segment (l ++ sub ++ r)))))
        ; try eassumption; try exact (classification_endpoint_spec l sub r Hspec).
      intros e He Hx.
      exact (classified_extension_segment_order_outside_gap
        l sub r Hspec LastEnd s e q (or_introl Hside) He Hq Hx).
    + assert (Hsub : In s sub).
      { repeat rewrite in_app_iff in Hin.
        rewrite in_app_iff in Hside. tauto. }
      intro Hp.
      pose proof (reconnected_sub_triangle_preimage l sub r h
        (length ls) s s' p Hspec Hh Hold Hnew Hsub Hp) as HsubTriangle.
      destruct (classic (r = [])) as [Hnil | Hnonempty].
      * assert (Hfix : classify l sub r (term (last_segment (l ++ sub ++ r))) = RegFix).
        {
        subst r. rewrite app_nil_r.
        rewrite (last_app_nonnil l sub Hne).
        apply (classified_sub_fixed l sub [] Hspec).
        apply onSegmentlist_term_last. exact Hne.
        }
        rewrite Hfix in Hshift. simpl in Hshift. subst p.
        exact (Houtside HsubTriangle).
      * apply (reconnect_extensions_avoid_sub_rect_from_spec
          l sub r h p Hne Hconn Hspec Hh Hsparse).
        -- right. split; assumption.
        -- exact (contained_sub_triangle sub s p
             (prepared_sub_contained l sub r Hgeom) Hsub HsubTriangle).
Qed.

(* 固定部分との分離と延長線の退避を合わせ、全域の三角形疎性を保存する。 *)
Lemma reconnect_preserves_sparse_embedding_prepared :
  forall ds l sub r h,
    PreparedGeometry l sub r ->
    @ClassificationSpec l sub r (classify l sub r) ->
    h_large h sub -> height_clears_sub h l sub r ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    sparse_embedding (reconnect_whole l sub r h).
Proof.
  intros ds l sub r h Hgeom Hspec Hh Hclear Hsparse Hembed Hext.
  apply geometric_triangle_sparse_embedding.
  - exact (reconnect_preserves_triangle_separation_from_prepared_spec
      ds l sub r h Hgeom Hspec Hh Hclear Hsparse Hembed).
  - exact (reconnect_preserves_triangle_extension_avoidance_from_prepared_spec
      ds l sub r h Hgeom Hspec Hh Hsparse Hembed Hext).
Qed.

End WithClassifier.
End ReconnectWholeByClassifier.

Definition split_nonadjacent_nth_errors := ReconnectWholeByClassifier.split_nonadjacent_nth_errors.
Definition nth_error_exists_at_equal_length := ReconnectWholeByClassifier.nth_error_exists_at_equal_length.
Definition region_delta := ReconnectWholeByClassifier.region_delta.
Definition region_delta_order := ReconnectWholeByClassifier.region_delta_order.
Definition shift_y_delta := ReconnectWholeByClassifier.shift_y_delta.
Definition reconnect_extensions_avoid_sub_rect_from_spec := ReconnectWholeByClassifier.reconnect_extensions_avoid_sub_rect_from_spec classify.
Definition reconnected_triangle_preimage := ReconnectWholeByClassifier.reconnected_triangle_preimage classify.
Definition classified_triangle_delta_order := ReconnectWholeByClassifier.classified_triangle_delta_order classify.
Definition shifted_point_avoids_reconnected_triangle := ReconnectWholeByClassifier.shifted_point_avoids_reconnected_triangle classify.
Definition reconnect_preserves_triangle_separation_prepared := ReconnectWholeByClassifier.reconnect_preserves_triangle_separation_prepared classify.
Definition reconnect_preserves_triangle_extension_avoidance_prepared := ReconnectWholeByClassifier.reconnect_preserves_triangle_extension_avoidance_prepared classify.
Definition reconnect_preserves_sparse_embedding_from_spec := ReconnectWholeByClassifier.reconnect_preserves_sparse_embedding_from_spec classify.
Definition ordinary_extensions_disjoint_prepared := ReconnectWholeByClassifier.ordinary_extensions_disjoint_prepared classify.
Definition ordinary_sparse_around_prepared := ReconnectWholeByClassifier.ordinary_sparse_around_prepared classify.

(* 準備済み埋め込みからの最終結論。 *)

(* 選んだ同一の分割埋め込みが三角形疎性を満たす。 *)
Record PreparedSparseEmbedding
    (ds1 sub_ds ds2 : list Direction)
    (l sub r : list Segment) : Prop := {
  prepared_left_embed : embed_listDir ds1 l;
  prepared_sub_embed : embed_listDir sub_ds sub;
  prepared_right_embed : embed_listDir ds2 r;
  prepared_whole_embed :
    embed_listDir (ds1 ++ sub_ds ++ ds2) (l ++ sub ++ r);
  prepared_whole_sparse : sparse_embedding (l ++ sub ++ r);
  prepared_extensions_disjoint : extensions_disjoint (l ++ sub ++ r);
  prepared_geometry : PreparedGeometry l sub r
}.

Section PreparedByClassifier.
Variable classifier : list Segment -> list Segment -> list Segment -> EndpointClassifier.
Local Notation reconnect_segs := (ReconnectByClassifier.reconnect_segs classifier).
Local Notation reconnect_whole := (ReconnectByClassifier.reconnect_whole classifier).
Local Notation reconnect_segs_length := (ReconnectLocalByClassifier.reconnect_segs_length classifier).
Local Notation prepared_reconnect_whole_preserves_embed :=
  (ReconnectLocalByClassifier.prepared_reconnect_whole_preserves_embed classifier).
Local Notation ordinary_extensions_disjoint_prepared :=
  (ReconnectWholeByClassifier.ordinary_extensions_disjoint_prepared classifier).
Local Notation ordinary_sparse_around_prepared :=
  (ReconnectWholeByClassifier.ordinary_sparse_around_prepared classifier).

(* prepared 証人から、sub を固定して両側を再接続する。
   全域疎性と局所疎性を両方結論に残す。 *)
Lemma embed_sparsely_prepared_from_spec :
  forall ds1 sub_ds ds2 l sub r,
    PreparedSparseEmbedding ds1 sub_ds ds2 l sub r ->
    @ClassificationSpec l sub r (classifier l sub r) ->
    exists l' r',
      embed_listDir ds1 l'
      /\ embed_listDir sub_ds sub
      /\ embed_listDir ds2 r'
      /\ embed_listDir (ds1 ++ sub_ds ++ ds2) (l' ++ sub ++ r')
      /\ sparse_embedding (l' ++ sub ++ r')
      /\ ~ close (l' ++ sub ++ r')
      /\ sparse_around l' sub r'.
Proof.
  intros ds1 sub_ds ds2 l sub r Hprepared Hspec.
  destruct Hprepared as [Hl Hsub Hr Hwhole Hsparse Hext Hgeometry].
  destruct (choose_height_clearing_sub l sub r) as [h [Hh Hclear]].
  set (l' := reconnect_segs l sub r h l).
  set (r' := reconnect_segs l sub r h r).
  assert (Hwhole' :
      embed_listDir (ds1 ++ sub_ds ++ ds2) (l' ++ sub ++ r')).
  { change (embed_listDir (ds1 ++ sub_ds ++ ds2)
              (reconnect_whole l sub r h)).
    exact (prepared_reconnect_whole_preserves_embed
             (ds1 ++ sub_ds ++ ds2) l sub r h
             (prepared_sub_nonempty l sub r Hgeometry) Hspec Hh Hsparse Hwhole Hext). }
  assert (HlenL : length ds1 = length l').
  { pose proof (embedding_listDir_length_consis ds1 l Hl) as Hlen.
    unfold l'. rewrite reconnect_segs_length. exact Hlen. }
  assert (HlenSub : length sub_ds = length sub).
  { exact (embedding_listDir_length_consis sub_ds sub Hsub). }
  assert (Hparts : embed_listDir ds1 l' /\
                   embed_listDir (sub_ds ++ ds2) (sub ++ r')).
  { change (embed_listDir (ds1 ++ (sub_ds ++ ds2))
              (l' ++ (sub ++ r'))) in Hwhole'.
    exact (embed_listDir_split_known
             ds1 (sub_ds ++ ds2) l' (sub ++ r') Hwhole' HlenL). }
  destruct Hparts as [Hleft HtailEmbed].
  assert (Hright : embed_listDir ds2 r').
  { exact (proj2 (embed_listDir_split_known
                    sub_ds ds2 sub r' HtailEmbed HlenSub)). }
  assert (Hsparse' : sparse_embedding (l' ++ sub ++ r')).
  { change (sparse_embedding (reconnect_whole l sub r h)).
    exact (ReconnectWholeByClassifier.reconnect_preserves_sparse_embedding_prepared
             classifier (ds1 ++ sub_ds ++ ds2) l sub r h
             Hgeometry Hspec Hh Hclear Hsparse Hwhole Hext). }
  assert (Hext' : extensions_disjoint (l' ++ sub ++ r')).
  { change (extensions_disjoint (reconnect_whole l sub r h)).
    exact (ordinary_extensions_disjoint_prepared
             (ds1 ++ sub_ds ++ ds2) l sub r h
             (prepared_sub_nonempty l sub r Hgeometry) Hspec Hh Hsparse Hwhole Hext). }
  assert (Hnonempty : l' ++ sub ++ r' <> []).
  { intro Hnil. apply app_eq_nil in Hnil as [_ Htail].
    apply app_eq_nil in Htail as [Hsubnil _].
    exact (prepared_sub_nonempty l sub r Hgeometry Hsubnil). }
  assert (Hopen : ~ close (l' ++ sub ++ r')).
  { exact (sparse_extensions_open _ _ Hnonempty Hwhole' Hsparse' Hext'). }
  assert (Haround : sparse_around l' sub r').
  { exact (ordinary_sparse_around_prepared
             (ds1 ++ sub_ds ++ ds2) l sub r h
             Hgeometry Hspec Hh Hclear Hsparse Hwhole Hext). }
  exists l', r'.
  split; [exact Hleft |].
  split; [exact Hsub |].
  split; [exact Hright |].
  split; [exact Hwhole' |].
  split; [exact Hsparse' |].
  split; [exact Hopen | exact Haround].
Qed.

End PreparedByClassifier.

(* 外部には具体的な分類仕様を見せず、固定した sub の結論だけを渡す。 *)
Proposition embed_sparsely_if_both_lids_removable
    (ds1 sub_ds ds2 : list Direction) (l sub r : list Segment) :
  PreparedSparseEmbedding ds1 sub_ds ds2 l sub r ->
  exists l' r',
    embed_listDir ds1 l'
    /\ embed_listDir sub_ds sub
    /\ embed_listDir ds2 r'
    /\ embed_listDir (ds1 ++ sub_ds ++ ds2) (l' ++ sub ++ r')
    /\ sparse_embedding (l' ++ sub ++ r')
    /\ ~ close (l' ++ sub ++ r')
    /\ sparse_around l' sub r'.
Proof.
  intro Hprepared.
  pose proof (prepared_geometry _ _ _ _ _ _ Hprepared) as Hgeometry.
  pose proof (prepared_whole_sparse _ _ _ _ _ _ Hprepared) as Hsparse.
  pose proof (prepared_whole_embed _ _ _ _ _ _ Hprepared) as Hwhole.
  pose proof (prepared_extensions_disjoint _ _ _ _ _ _ Hprepared) as Hext.
  destruct (prepared_classification_exists l sub r Hgeometry Hsparse
    (ex_intro _ (ds1 ++ sub_ds ++ ds2) Hwhole) Hext) as [classifier Hspec].
  exact (embed_sparsely_prepared_from_spec (fun _ _ _ => classifier)
    ds1 sub_ds ds2 l sub r Hprepared Hspec).
Qed.
