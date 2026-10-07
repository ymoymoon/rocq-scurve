Require Export Sparse.ReconnectLocalProof.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.

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
  destruct Hextend as [[Hl Hhead] | [Hr Hlast]].
  - destruct (reconnect_head_strict_extension_preimage_from_spec
                l sub r h p Hne Hsparse Hspec
                (Rlt_le _ _ (proj1 Hh)) Hhead)
      as [q [Hq Hshift]].
    set (g := classify l sub r
                (init (hd_segment (l ++ sub ++ r)))).
    eapply (classified_shifted_extension_avoids_sub_rect_from_spec
              l sub r h p q g Hne HconnSub Hspec Hh).
    + now left.
    + intros Hg z [s [Hs Hz]] Hx Hy. exfalso.
      assert (Hin : In s (l ++ sub ++ r)).
      { rewrite !in_app_iff. right; left; exact Hs. }
      pose proof (proj1
        (classified_head_segment_crossing_order
           l sub r
           Hspec
           s z q Hin Hz Hq ltac:(symmetry; exact Hx)) Hy)
        as [HinitOrder _].
      change
        (classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegUp)
        in Hg.
      rewrite Hg in HinitOrder.
      pose proof (region_at_or_above_RegUp_inv _ HinitOrder) as HinitUp.
      pose proof (classified_sub_fixed
                    l sub r
                    Hspec
                    (init s)
                    ltac:(exists s; split; [exact Hs | apply onInit]))
        as HinitFix.
      congruence.
    + intros Hg z [s [Hs Hz]] Hx Hy. exfalso.
      assert (Hin : In s (l ++ sub ++ r)).
      { rewrite !in_app_iff. right; left; exact Hs. }
      pose proof (proj2
        (classified_head_segment_crossing_order
           l sub r
           Hspec
           s z q Hin Hz Hq ltac:(symmetry; exact Hx)) Hy)
        as [HinitOrder _].
      change
        (classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegDown)
        in Hg.
      rewrite Hg in HinitOrder.
      pose proof (RegDown_at_or_above_inv _ HinitOrder) as HinitDown.
      pose proof (classified_sub_fixed
                    l sub r
                    Hspec
                    (init s)
                    ltac:(exists s; split; [exact Hs | apply onInit]))
        as HinitFix.
      congruence.
    + intros Hx.
      exact (classified_head_extension_at_sub_x
               l sub r
               Hspec
               Hl q Hq Hx).
    + exact Hshift.
  - destruct (reconnect_last_strict_extension_preimage_from_spec
                l sub r h p Hne Hsparse Hspec
                (Rlt_le _ _ (proj1 Hh)) Hlast)
      as [q [Hq Hshift]].
    set (g := classify l sub r
                (term (last_segment (l ++ sub ++ r)))).
    eapply (classified_shifted_extension_avoids_sub_rect_from_spec
              l sub r h p q g Hne HconnSub Hspec Hh).
    + now right.
    + intros Hg z [s [Hs Hz]] Hx Hy. exfalso.
      assert (Hin : In s (l ++ sub ++ r)).
      { rewrite !in_app_iff. right; left; exact Hs. }
      pose proof (proj1
        (classified_last_segment_crossing_order
           l sub r
           Hspec
           s z q Hin Hz Hq ltac:(symmetry; exact Hx)) Hy)
        as [HinitOrder _].
      change
        (classify l sub r (term (last_segment (l ++ sub ++ r))) = RegUp)
        in Hg.
      rewrite Hg in HinitOrder.
      pose proof (region_at_or_above_RegUp_inv _ HinitOrder) as HinitUp.
      pose proof (classified_sub_fixed
                    l sub r
                    Hspec
                    (init s)
                    ltac:(exists s; split; [exact Hs | apply onInit]))
        as HinitFix.
      congruence.
    + intros Hg z [s [Hs Hz]] Hx Hy. exfalso.
      assert (Hin : In s (l ++ sub ++ r)).
      { rewrite !in_app_iff. right; left; exact Hs. }
      pose proof (proj2
        (classified_last_segment_crossing_order
           l sub r
           Hspec
           s z q Hin Hz Hq ltac:(symmetry; exact Hx)) Hy)
        as [HinitOrder _].
      change
        (classify l sub r (term (last_segment (l ++ sub ++ r))) = RegDown)
        in Hg.
      rewrite Hg in HinitOrder.
      pose proof (RegDown_at_or_above_inv _ HinitOrder) as HinitDown.
      pose proof (classified_sub_fixed
                    l sub r
                    Hspec
                    (init s)
                    ltac:(exists s; split; [exact Hs | apply onInit]))
        as HinitFix.
      congruence.
    + intros Hx.
      exact (classified_last_extension_at_sub_x
               l sub r
               Hspec
               Hr q Hq Hx).
    + exact Hshift.
Qed.

(* 新しい閉三角形の点を、同じ出現の旧三角形へ引き戻す。 *)
Lemma reconnected_triangle_preimage :
  forall l sub r h i s s' z,
    @ReconnectClassificationSpec l sub r (classify l sub r) ->
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
    @ReconnectClassificationSpec l sub r (classify l sub r) ->
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
    @ReconnectClassificationSpec l sub r (classify l sub r) ->
    h_large h sub ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (reconnect_whole l sub r h) i = Some s' ->
    ~ in_segment_triangle s q ->
    z = shift h g q ->
    (forall e,
       onSegment s e -> fst e = fst q ->
       (snd q < snd e ->
          region_at_or_above (classify l sub r (init s)) g /\
          region_at_or_above (classify l sub r (term s)) g) /\
       (snd e < snd q ->
          region_at_or_above g (classify l sub r (init s)) /\
          region_at_or_above g (classify l sub r (term s)))) ->
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
    @ReconnectClassificationSpec l sub r (classify l sub r) ->
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
    @ReconnectClassificationSpec l sub r (classify l sub r) ->
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
      ; try eassumption.
    intros e He Hx.
    exact (classified_head_segment_crossing_order
      l sub r Hspec s e q Hin He Hq Hx).
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
      ; try eassumption.
    intros e He Hx.
    exact (classified_last_segment_crossing_order
      l sub r Hspec s e q Hin He Hq Hx).
Qed.

(* 蓋や局所退避条件ではなく、共通の三角形順序だけから全域疎性を保存する。 *)
Lemma reconnect_preserves_sparse_embedding_from_spec :
  forall ds l sub r h,
    sub <> [] ->
    @ReconnectClassificationSpec l sub r (classify l sub r) ->
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
    @ReconnectClassificationSpec l sub r (classify l sub r) ->
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
               l sub r h s Hne Hconn Hclear Hsparse Hspec Hs).
    + exact Hp.
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

(* prepared 証人から、sub を固定して両側を再接続する。
   全域疎性と局所疎性を両方結論に残す。 *)
Lemma embed_sparsely_prepared_from_spec :
  forall ds1 sub_ds ds2 l sub r,
    PreparedSparseEmbedding ds1 sub_ds ds2 l sub r ->
    @ClassificationSpec l sub r (classify l sub r) ->
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
    exact (reconnect_preserves_sparse_embedding_from_spec
             (ds1 ++ sub_ds ++ ds2) l sub r h
             (prepared_sub_nonempty l sub r Hgeometry) Hspec Hh Hsparse Hwhole Hext). }
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
  eapply embed_sparsely_prepared_from_spec; [exact Hprepared |].
  destruct Hprepared as [_ _ _ Hwhole Hsparse Hext Hgeometry].
  exact (classify_spec l sub r Hgeometry Hsparse
           (ex_intro _ (ds1 ++ sub_ds ++ ds2) Hwhole) Hext).
Qed.
