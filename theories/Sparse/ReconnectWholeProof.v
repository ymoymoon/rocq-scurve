Require Export Sparse.ReconnectLocalProof.
Import PreparedReconnect.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.

Module PreparedReconnectWhole.

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

(* 再接続した全体の延長線は、非隣接セグメントの長方形を避ける。 *)
Lemma reconnect_preserves_extensions_avoid_rectangles_from_spec :
  forall l sub r h,
    sub <> [] ->
    ClassificationSpec l sub r ->
    h_large h sub ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    sparse_embedding (l ++ sub ++ r) ->
    extensions_avoid_segment_rectangles (reconnect_whole l sub r h).
Proof.
  intros l sub r h Hne Hspec Hh Hrec Hsparse.
  unfold extensions_avoid_segment_rectangles.
  intros l' s' r' Hsplit p Hextension Hp.
  assert (Hs' :
    nth_error (reconnect_whole l sub r h) (length l') = Some s').
  { rewrite Hsplit, nth_error_app2 by lia.
    replace (length l' - length l')%nat with 0%nat by lia.
    reflexivity. }
  assert (Hlen :
    length (l ++ sub ++ r) = length (reconnect_whole l sub r h)).
  { symmetry. apply reconnect_whole_length. }
  destruct (nth_error_exists_at_equal_length
              (l ++ sub ++ r) (reconnect_whole l sub r h)
              (length l') s' Hlen Hs') as [s Hs].
  assert (Hin : In s (l ++ sub ++ r)).
  { now apply nth_error_In in Hs. }
  destruct (@nth_error_split Segment (l ++ sub ++ r) (length l') s Hs)
    as [oldl [oldr [HoldSplit HoldLen]]].
  destruct (Hsparse oldl s oldr HoldSplit) as [HoldExtension _].
  pose proof (reconnect_whole_nth_spec
                l sub r h (length l') s s' Hspec Hrec Hs Hs')
    as [_ [Hinit Hterm]].
  destruct Hextension as [[Hl' Hhead] | [Hr' Hlast]].
  - destruct (reconnect_head_strict_extension_preimage_from_spec
                l sub r h p Hne Hsparse Hspec
                (Rlt_le _ _ (proj1 Hh)) Hhead)
      as [q [Hq Hpoint]].
    rewrite Hpoint in Hp.
    eapply (shifted_crossing_avoids_endpoint_rect
              h s s' q
              (classify l sub r
                 (init (hd_segment (l ++ sub ++ r))))
              (classify l sub r (init s))
              (classify l sub r (term s))).
    + exact (proj1 Hh).
    + unfold operate_point in Hinit. exact Hinit.
    + unfold operate_point in Hterm. exact Hterm.
    + apply (HoldExtension q). left. split.
      * intros Holdnil. subst oldl. simpl in HoldLen.
        apply Hl'. apply length_zero_iff_nil. lia.
      * change (onHead_extend_strict (oldl ++ s :: oldr) q).
        now rewrite <- HoldSplit.
    + intros e He Hxe.
      exact (classified_head_segment_crossing_order
               l sub r Hspec s e q Hin He Hq Hxe).
    + exact Hp.
  - destruct (reconnect_last_strict_extension_preimage_from_spec
                l sub r h p Hne Hsparse Hspec
                (Rlt_le _ _ (proj1 Hh)) Hlast)
      as [q [Hq Hpoint]].
    rewrite Hpoint in Hp.
    eapply (shifted_crossing_avoids_endpoint_rect
              h s s' q
              (classify l sub r
                 (term (last_segment (l ++ sub ++ r))))
              (classify l sub r (init s))
              (classify l sub r (term s))).
    + exact (proj1 Hh).
    + unfold operate_point in Hinit. exact Hinit.
    + unfold operate_point in Hterm. exact Hterm.
    + apply (HoldExtension q). right. split.
      * intros Holdnil. subst oldr. simpl in HoldSplit.
        assert (Hlengths := Hlen).
        rewrite HoldSplit, Hsplit in Hlengths.
        rewrite !length_app in Hlengths. simpl in Hlengths.
        apply Hr'. apply length_zero_iff_nil. lia.
      * change (onLast_extend_strict (oldl ++ s :: oldr) q).
        now rewrite <- HoldSplit.
    + intros e He Hxe.
      exact (classified_last_segment_crossing_order
               l sub r Hspec s e q Hin He Hq Hxe).
    + exact Hp.
Qed.

(* 十分大きな移動後、全体の延長線は sub の長方形を避ける。 *)
Lemma reconnect_extensions_avoid_sub_rect_from_spec :
  forall l sub r h p,
    sub <> [] ->
    connected sub ->
    ClassificationSpec l sub r ->
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
               q Hq Hx).
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
               q Hq Hx).
    + exact Hshift.
Qed.

(* 元の sparse 列では、二つ以上離れた出現の閉端点長方形は
   水平または垂直のいずれかに厳密分離している。 *)
Lemma sparse_far_rectangles_axis_separated :
  forall ls i j s t,
    sparse_embedding ls ->
    nth_error ls i = Some s ->
    nth_error ls j = Some t ->
    (S i < j \/ S j < i)%nat ->
    endpoint_rectangles_axis_separated s t.
Proof.
  intros ls i j s t Hsparse Hs Ht Hfar.
  destruct (nth_error_far_in_nonadjacent_sides ls i j s t Hs Ht Hfar)
    as [before [after [Hsplit Hin]]].
  apply rectangles_avoid_implies_axis_separated.
  intros p Htp.
  exact ((proj2 (Hsparse before s after Hsplit)) t p Hin Htp).
Qed.

(* 添字ごとの閉長方形分離と延長線回避を全域 sparse に変換する。 *)
Lemma indexed_far_rectangles_give_sparse_embedding :
  forall ls,
    (forall i j s t,
      nth_error ls i = Some s ->
      nth_error ls j = Some t ->
      (S i < j \/ S j < i)%nat ->
      endpoint_rectangles_axis_separated s t) ->
    extensions_avoid_segment_rectangles ls ->
    sparse_embedding ls.
Proof.
  intros ls Hfar Hext.
  apply geometric_sparse_embedding; [|exact Hext].
  unfold segment_rectangles_separated.
  intros left s right Hsplit t Hin p Hp.
  destruct (split_nonadjacent_nth_errors ls left s right t Hsplit Hin)
    as [i [j [Hs [Ht Hij]]]].
  exact (axis_separated_boxes_avoid s t (Hfar i j s t Hs Ht Hij) p Hp).
Qed.

(* strict 延長線の順序証明を、prepared 分類へ輸送する残りの枝。 *)
Lemma ordinary_extensions_avoid_rectangles_prepared :
  forall ds l sub r h,
    PreparedGeometry l sub r ->
    ClassificationSpec l sub r ->
    connected sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    extensions_avoid_segment_rectangles
      (reconnect_whole l sub r h).
Proof.
  intros ds l sub r h Hgeometry Hspec Hconn Hh Hsparse Hembed Hext.
  assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
  { exact (operate_endpoints_reconnectable_from_spec
             l sub r h Hspec Hh). }
  exact (reconnect_preserves_extensions_avoid_rectangles_from_spec
           l sub r h (prepared_sub_nonempty l sub r Hgeometry)
           Hspec Hh Hrec Hsparse).
Qed.

(* 蓋なし順序仕様があれば、境界出現も通常出現も一律に分離する。 *)
Lemma prepared_no_lid_preserves_sparse_embedding :
  forall ds l sub r h,
    PreparedGeometry l sub r ->
    ClassificationSpec l sub r ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    sparse_embedding (reconnect_whole l sub r h).
Proof.
  intros ds l sub r h Hgeometry Hspec Hh Hsparse Hembed Hext.
  assert (Hconn : connected sub).
  { eapply connected_middle.
    exact (embed_listDir_connected ds _ Hembed). }
  assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
  { exact (operate_endpoints_reconnectable_from_spec
             l sub r h Hspec Hh). }
  apply indexed_far_rectangles_give_sparse_embedding.
  - intros i j s t Hs Ht Hfar.
    assert (Hlen :
        length (l ++ sub ++ r) =
        length (reconnect_whole l sub r h)).
    { symmetry. apply reconnect_whole_length. }
    destruct (nth_error_exists_at_equal_length
                (l ++ sub ++ r) (reconnect_whole l sub r h)
                i s Hlen Hs) as [old_s HoldS].
    destruct (nth_error_exists_at_equal_length
                (l ++ sub ++ r) (reconnect_whole l sub r h)
                j t Hlen Ht) as [old_t HoldT].
    pose proof (reconnect_whole_nth_spec
                  l sub r h i old_s s Hspec Hrec HoldS Hs)
      as [_ [HinitS HtermS]].
    pose proof (reconnect_whole_nth_spec
                  l sub r h j old_t t Hspec Hrec HoldT Ht)
      as [_ [HinitT HtermT]].
    eapply operated_endpoint_rectangles_axis_separated_no_lid.
    + exact Hspec.
    + exact (prepared_no_terminal_lid l sub r Hgeometry).
    + exact (prepared_no_initial_lid l sub r Hgeometry).
    + exact (proj1 Hh).
    + exact HoldS.
    + exact HoldT.
    + exact Hfar.
    + exact HinitS.
    + exact HtermS.
    + exact HinitT.
    + exact HtermT.
    + exact (sparse_far_rectangles_axis_separated
               (l ++ sub ++ r) i j old_s old_t
               Hsparse HoldS HoldT Hfar).
  - exact (ordinary_extensions_avoid_rectangles_prepared
             ds l sub r h Hgeometry Hspec Hconn Hh Hsparse Hembed Hext).
Qed.

(* 分類仕様の延長線順序を使い、再接続後の延長線非交差を示す。 *)
Lemma ordinary_extensions_disjoint_prepared :
  forall ds l sub r h,
    PreparedGeometry l sub r ->
    ClassificationSpec l sub r ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    extensions_disjoint (reconnect_whole l sub r h).
Proof.
  intros ds l sub r h Hgeometry Hspec Hh Hsparse Hembed Hext.
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
              (prepared_sub_nonempty l sub r Hgeometry)
              Hspec HheadSlope Hhead)
    as [ph [Hph HshiftHead]].
  destruct (reconnect_last_extension_preimage_from_spec
              l sub r h p
              (prepared_sub_nonempty l sub r Hgeometry)
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
    ClassificationSpec l sub r ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    sparse_around
      (reconnect_segs l sub r h l) sub
      (reconnect_segs l sub r h r).
Proof.
  intros ds l sub r h Hgeometry Hspec Hh Hsparse Hembed Hext.
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
               l sub r h s Hne Hconn Hh Hsparse Hspec Hs).
    + exact Hp.
Qed.

(* 準備済み埋め込みからの最終結論。 *)

(* 選んだ同一の分割埋め込みが、全域疎性と分類に必要な prepared 幾何を満たす。 *)
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
    ClassificationSpec l sub r ->
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
  destruct (choose_h sub) as [h Hh].
  set (l' := reconnect_segs l sub r h l).
  set (r' := reconnect_segs l sub r h r).
  assert (Hwhole' :
      embed_listDir (ds1 ++ sub_ds ++ ds2) (l' ++ sub ++ r')).
  { change (embed_listDir (ds1 ++ sub_ds ++ ds2)
              (reconnect_whole l sub r h)).
    exact (prepared_reconnect_whole_preserves_embed
             (ds1 ++ sub_ds ++ ds2) l sub r h
             Hgeometry Hspec Hh Hsparse Hwhole Hext). }
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
    exact (prepared_no_lid_preserves_sparse_embedding
             (ds1 ++ sub_ds ++ ds2) l sub r h
             Hgeometry Hspec Hh Hsparse Hwhole Hext). }
  assert (Hext' : extensions_disjoint (l' ++ sub ++ r')).
  { change (extensions_disjoint (reconnect_whole l sub r h)).
    exact (ordinary_extensions_disjoint_prepared
             (ds1 ++ sub_ds ++ ds2) l sub r h
             Hgeometry Hspec Hh Hsparse Hwhole Hext). }
  assert (Hnonempty : l' ++ sub ++ r' <> []).
  { intro Hnil. apply app_eq_nil in Hnil as [_ Htail].
    apply app_eq_nil in Htail as [Hsubnil _].
    exact (prepared_sub_nonempty l sub r Hgeometry Hsubnil). }
  assert (Hopen : ~ close (l' ++ sub ++ r')).
  { exact (sparse_extensions_open _ _ Hnonempty Hwhole' Hsparse' Hext'). }
  assert (Haround : sparse_around l' sub r').
  { exact (ordinary_sparse_around_prepared
             (ds1 ++ sub_ds ++ ds2) l sub r h
             Hgeometry Hspec Hh Hsparse Hwhole Hext). }
  exists l', r'.
  split; [exact Hleft |].
  split; [exact Hsub |].
  split; [exact Hright |].
  split; [exact Hwhole' |].
  split; [exact Hsparse' |].
  split; [exact Hopen | exact Haround].
Qed.

End PreparedReconnectWhole.

(* 公開する prepared 入力。蓋のない初期埋め込みについて、通常再接続後も
   全域 sparse 性を保つ最終結論の入力を一箇所にまとめる。 *)
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

(* Spec を仮定した prepared 再接続の全域結論。 *)
Lemma embed_sparsely_prepared_from_spec
    (ds1 sub_ds ds2 : list Direction) (l sub r : list Segment) :
  PreparedSparseEmbedding ds1 sub_ds ds2 l sub r ->
  ClassificationSpec l sub r ->
  exists l' r',
    embed_listDir ds1 l'
    /\ embed_listDir sub_ds sub
    /\ embed_listDir ds2 r'
    /\ embed_listDir (ds1 ++ sub_ds ++ ds2) (l' ++ sub ++ r')
    /\ sparse_embedding (l' ++ sub ++ r')
    /\ ~ close (l' ++ sub ++ r')
    /\ sparse_around l' sub r'.
Proof.
  intros Hprepared Hspec.
  destruct Hprepared as [Hl Hsub Hr Hwhole Hsparse Hext Hgeometry].
  eapply PreparedReconnectWhole.embed_sparsely_prepared_from_spec.
  - refine
      (PreparedReconnectWhole.Build_PreparedSparseEmbedding
         ds1 sub_ds ds2 l sub r Hl Hsub Hr Hwhole Hsparse Hext Hgeometry).
  - exact Hspec.
Qed.

(* 分類の正しさだけを隠した公開版。 *)
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
  eapply classify_spec; eauto.
Qed.
