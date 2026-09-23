Require Export Sparse.ReconnectProof.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.

(* 再接続による長方形・延長線・sub 周辺の分離保存。 *)
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

Definition endpoint_rectangles_axis_separated (s t : Segment) : Prop :=
     rx1 (rect_of [t]) < rx0 (rect_of [s])
  \/ rx1 (rect_of [s]) < rx0 (rect_of [t])
  \/ ry1 (rect_of [t]) < ry0 (rect_of [s])
  \/ ry1 (rect_of [s]) < ry0 (rect_of [t]).

Lemma singleton_rect_positive : forall s,
  rx0 (rect_of [s]) < rx1 (rect_of [s])
  /\ ry0 (rect_of [s]) < ry1 (rect_of [s]).
Proof.
  intros s. unfold rect_of; simpl. split.
  - destruct (total_order_T (fst (init s)) (fst (term s)))
      as [[Hlt | Heq] | Hgt].
    + rewrite Rmin_left by now apply Rlt_le.
      rewrite Rmax_right by now apply Rlt_le. exact Hlt.
    + exfalso. apply (neq_init_term_x s). exact Heq.
    + rewrite Rmin_right by now apply Rlt_le.
      rewrite Rmax_left by now apply Rlt_le. exact Hgt.
  - destruct (total_order_T (snd (init s)) (snd (term s)))
      as [[Hlt | Heq] | Hgt].
    + rewrite Rmin_left by now apply Rlt_le.
      rewrite Rmax_right by now apply Rlt_le. exact Hlt.
    + exfalso. apply (neq_init_term_y s). exact Heq.
    + rewrite Rmin_right by now apply Rlt_le.
      rewrite Rmax_left by now apply Rlt_le. exact Hgt.
Qed.

(* 一方の端点長方形が他方を避ければ、二長方形は軸方向に分離する。 *)
Lemma rectangles_avoid_implies_axis_separated : forall s t,
  (forall p,
    in_segment_rect_or_endpoints t p ->
    ~ in_rect_or_endpoints_at [s] p) ->
  endpoint_rectangles_axis_separated s t.
Proof.
  intros s t Havoid. unfold endpoint_rectangles_axis_separated.
  destruct (classic (rx1 (rect_of [t]) < rx0 (rect_of [s]))) as [H | H]; [now left|].
  destruct (classic (rx1 (rect_of [s]) < rx0 (rect_of [t]))) as [H' | H']; [now right; left|].
  destruct (classic (ry1 (rect_of [t]) < ry0 (rect_of [s]))) as [Hy | Hy]; [now right; right; left|].
  destruct (classic (ry1 (rect_of [s]) < ry0 (rect_of [t]))) as [Hy' | Hy']; [now right; right; right|].
  destruct (singleton_rect_positive s) as [Hsx Hsy].
  destruct (singleton_rect_positive t) as [Htx Hty].
  set (x := Rmax (rx0 (rect_of [s])) (rx0 (rect_of [t]))).
  set (y := Rmax (ry0 (rect_of [s])) (ry0 (rect_of [t]))).
  assert (Hxs : rx0 (rect_of [s]) <= x <= rx1 (rect_of [s])).
  { split; [unfold x; apply Rmax_l |].
    unfold x. apply Rmax_lub; [lra | now apply Rnot_lt_le]. }
  assert (Hxt : rx0 (rect_of [t]) <= x <= rx1 (rect_of [t])).
  { split; [unfold x; apply Rmax_r |].
    unfold x. apply Rmax_lub; [now apply Rnot_lt_le | lra]. }
  assert (Hys : ry0 (rect_of [s]) <= y <= ry1 (rect_of [s])).
  { split; [unfold y; apply Rmax_l |].
    unfold y. apply Rmax_lub; [lra | now apply Rnot_lt_le]. }
  assert (Hyt : ry0 (rect_of [t]) <= y <= ry1 (rect_of [t])).
  { split; [unfold y; apply Rmax_r |].
    unfold y. apply Rmax_lub; [now apply Rnot_lt_le | lra]. }
  exfalso.
  apply (Havoid (x, y)).
  - unfold in_segment_rect_or_endpoints, in_closed_rect; simpl.
    exact (conj Hxt Hyt).
  - unfold in_rect_or_endpoints_at, in_closed_rect; simpl.
    exact (conj Hxs Hys).
Qed.

Lemma in_segment_rect_or_endpoints_closed_bounds : forall s p,
  in_segment_rect_or_endpoints s p ->
  rx0 (rect_of [s]) <= fst p <= rx1 (rect_of [s])
  /\ ry0 (rect_of [s]) <= snd p <= ry1 (rect_of [s]).
Proof.
  intros s p Hp. exact Hp.
Qed.

(* 軸方向に厳密に分離した二閉長方形は互いに交わらない。 *)
Lemma axis_separated_boxes_avoid : forall s t,
  endpoint_rectangles_axis_separated s t ->
  forall p,
    in_segment_rect_or_endpoints t p ->
    ~ in_rect_or_endpoints_at [s] p.
Proof.
  intros s t Haxis p Hp Hs.
  unfold in_segment_rect_or_endpoints, in_rect_or_endpoints_at,
    in_closed_rect in Hp, Hs.
  unfold endpoint_rectangles_axis_separated in Haxis.
  destruct Haxis as [Haxis | [Haxis | [Haxis | Haxis]]]; lra.
Qed.

(* 端点間の分類順序により、旧長方形の軸方向の分離は移動後も保たれる。 *)
Lemma operated_endpoint_rectangles_axis_separated :
  forall l sub r h i j s t s' t',
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    0 < h ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (l ++ sub ++ r) j = Some t ->
    (S i < j \/ S j < i)%nat ->
    init s' = operate_point l sub r h (init s) ->
    term s' = operate_point l sub r h (term s) ->
    init t' = operate_point l sub r h (init t) ->
    term t' = operate_point l sub r h (term t) ->
    ~ onSegmentlist sub (init s) ->
    ~ onSegmentlist sub (term s) ->
    ~ onSegmentlist sub (init t) ->
    ~ onSegmentlist sub (term t) ->
    endpoint_rectangles_axis_separated s t ->
    endpoint_rectangles_axis_separated s' t'.
Proof.
  intros l sub r h i j s t s' t' Hne Hconn Hmono Hsparse Hwhole Hembedded Hext Hh
    Hs Ht Hfar Hsinit Hsterm Htinit Htterm
    HsinitNotSub HstermNotSub HtinitNotSub HttermNotSub Haxis.
  assert (Horder :
    forall i0 j0 u v pu pv,
      nth_error (l ++ sub ++ r) i0 = Some u ->
      nth_error (l ++ sub ++ r) j0 = Some v ->
      (S i0 < j0 \/ S j0 < i0)%nat ->
      segment_x_ranges_overlap u v ->
      endpoint_of_seg u pu -> endpoint_of_seg v pv ->
      ~ onSegmentlist sub pv ->
      snd pu < snd pv ->
      snd (operate_point l sub r h pu) <
      snd (operate_point l sub r h pv)).
  { intros i0 j0 u v pu pv Hu Hv Hfar0 Hoverlap Hpu Hpv HpvNotSub Hy.
    unfold operate_point. eapply shift_preserves_strict_vertical_order;
      [exact Hh | exact Hy |].
    exact (classified_nonadjacent_endpoint_order
             l sub r
             (classify_spec l sub r Hne Hmono Hsparse Hembedded Hext)
             i0 j0 u v pu pv Hu Hv Hfar0 Hoverlap Hpu Hpv
             HpvNotSub (Rlt_le _ _ Hy)). }
  unfold endpoint_rectangles_axis_separated in Haxis |- *.
  assert (Hhorizontal_or_overlap :
      rx1 (rect_of [t]) < rx0 (rect_of [s])
      \/ rx1 (rect_of [s]) < rx0 (rect_of [t])
      \/ segment_x_ranges_overlap s t).
  { destruct (classic (rx1 (rect_of [t]) < rx0 (rect_of [s])))
      as [Hleft | Hleft]; [now left|].
    destruct (classic (rx1 (rect_of [s]) < rx0 (rect_of [t])))
      as [Hright | Hright]; [now right; left|].
    right; right. unfold segment_x_ranges_overlap. lra. }
  destruct Hhorizontal_or_overlap as [Hleft | [Hright | Hoverlap]].
  - left.
    change (Rmax (fst (init t')) (fst (term t')) <
            Rmin (fst (init s')) (fst (term s'))).
    change (Rmax (fst (init t)) (fst (term t)) <
            Rmin (fst (init s)) (fst (term s))) in Hleft.
    rewrite Hsinit, Hsterm, Htinit, Htterm.
    rewrite !operate_point_fst. exact Hleft.
  - right; left.
    change (Rmax (fst (init s')) (fst (term s')) <
            Rmin (fst (init t')) (fst (term t'))).
    change (Rmax (fst (init s)) (fst (term s)) <
            Rmin (fst (init t)) (fst (term t))) in Hright.
    rewrite Hsinit, Hsterm, Htinit, Htterm.
    rewrite !operate_point_fst. exact Hright.
  - destruct Haxis as [Hleft' | [Hright' | [Hbelow | Habove]]].
    + unfold segment_x_ranges_overlap in Hoverlap. lra.
    + unfold segment_x_ranges_overlap in Hoverlap. lra.
    + right; right; left.
    change (Rmax (snd (init t')) (snd (term t')) <
            Rmin (snd (init s')) (snd (term s'))).
    rewrite Hsinit, Hsterm, Htinit, Htterm.
    change (Rmax (snd (init t)) (snd (term t)) <
            Rmin (snd (init s)) (snd (term s))) in Hbelow.
    assert (Hold : forall pt ps,
      endpoint_of_seg t pt -> endpoint_of_seg s ps -> snd pt < snd ps).
    { intros pt ps Hpt Hps. destruct Hpt as [-> | ->]; destruct Hps as [-> | ->];
        pose proof (Rmax_l (snd (init t)) (snd (term t)));
        pose proof (Rmax_r (snd (init t)) (snd (term t)));
        pose proof (Rmin_l (snd (init s)) (snd (term s)));
        pose proof (Rmin_r (snd (init s)) (snd (term s))); lra. }
    assert (Hfar' : (S j < i \/ S i < j)%nat) by tauto.
    assert (Hoverlap' : segment_x_ranges_overlap t s).
    { unfold segment_x_ranges_overlap in *. tauto. }
    apply Rmax_lub_lt; apply Rmin_glb_lt.
    * eapply (Horder j i t s (init t) (init s));
        [exact Ht | exact Hs | exact Hfar' | exact Hoverlap' |
         now left | now left | exact HsinitNotSub |
         apply Hold; now left].
    * eapply (Horder j i t s (init t) (term s));
        [exact Ht | exact Hs | exact Hfar' | exact Hoverlap' |
         now left | now right | exact HstermNotSub |
         apply Hold; [now left | now right]].
    * eapply (Horder j i t s (term t) (init s));
        [exact Ht | exact Hs | exact Hfar' | exact Hoverlap' |
         now right | now left | exact HsinitNotSub |
         apply Hold; [now right | now left]].
    * eapply (Horder j i t s (term t) (term s));
        [exact Ht | exact Hs | exact Hfar' | exact Hoverlap' |
         now right | now right | exact HstermNotSub |
         apply Hold; now right].
    + right; right; right.
    change (Rmax (snd (init s')) (snd (term s')) <
            Rmin (snd (init t')) (snd (term t'))).
    rewrite Hsinit, Hsterm, Htinit, Htterm.
    change (Rmax (snd (init s)) (snd (term s)) <
            Rmin (snd (init t)) (snd (term t))) in Habove.
    assert (Hold : forall ps pt,
      endpoint_of_seg s ps -> endpoint_of_seg t pt -> snd ps < snd pt).
    { intros ps pt Hps Hpt. destruct Hps as [-> | ->]; destruct Hpt as [-> | ->];
        pose proof (Rmax_l (snd (init s)) (snd (term s)));
        pose proof (Rmax_r (snd (init s)) (snd (term s)));
        pose proof (Rmin_l (snd (init t)) (snd (term t)));
        pose proof (Rmin_r (snd (init t)) (snd (term t))); lra. }
    apply Rmax_lub_lt; apply Rmin_glb_lt.
    * eapply (Horder i j s t (init s) (init t));
        [exact Hs | exact Ht | exact Hfar | exact Hoverlap |
         now left | now left | exact HtinitNotSub |
         apply Hold; now left].
    * eapply (Horder i j s t (init s) (term t));
        [exact Hs | exact Ht | exact Hfar | exact Hoverlap |
         now left | now right | exact HttermNotSub |
         apply Hold; [now left | now right]].
    * eapply (Horder i j s t (term s) (init t));
        [exact Hs | exact Ht | exact Hfar | exact Hoverlap |
         now right | now left | exact HtinitNotSub |
         apply Hold; [now right | now left]].
    * eapply (Horder i j s t (term s) (term t));
        [exact Hs | exact Ht | exact Hfar | exact Hoverlap |
         now right | now right | exact HttermNotSub |
         apply Hold; now right].
Qed.

(* 延長線点と同じ x の旧セグメント点が与える分類順序から，
   延長線点は移動後の端点長方形にも入らない。 *)
Lemma shifted_crossing_avoids_endpoint_rect :
  forall h s s' q g gi gt,
    0 < h ->
    init s' = shift h gi (init s) ->
    term s' = shift h gt (term s) ->
    ~ in_rect_or_endpoints_at [s] q ->
    (forall e,
      onSegment s e ->
      fst e = fst q ->
      (snd q < snd e ->
         region_at_or_above gi g /\ region_at_or_above gt g)
      /\
      (snd e < snd q ->
         region_at_or_above g gi /\ region_at_or_above g gt)) ->
    ~ in_rect_or_endpoints_at [s'] (shift h g q).
Proof.
  intros h s s' q g gi gt Hh Hinit Hterm Hold Hcross Hnew.
  unfold in_rect_or_endpoints_at, in_closed_rect in Hold, Hnew.
  change
    (~ ((Rmin (fst (init s)) (fst (term s)) <= fst q <=
          Rmax (fst (init s)) (fst (term s))) /\
         (Rmin (snd (init s)) (snd (term s)) <= snd q <=
          Rmax (snd (init s)) (snd (term s))))) in Hold.
  change
    ((Rmin (fst (init s')) (fst (term s')) <= fst (shift h g q) <=
       Rmax (fst (init s')) (fst (term s'))) /\
     (Rmin (snd (init s')) (snd (term s')) <= snd (shift h g q) <=
       Rmax (snd (init s')) (snd (term s')))) in Hnew.
  rewrite Hinit, Hterm, !shift_fst in Hnew.
  destruct Hnew as [Hqx Hqy].
  destruct (segment_has_point_at_x s (fst q) Hqx) as [e [He Hxe]].
  pose proof (segment_in_rect_or_endpoints s e He) as Hebounds.
  unfold in_segment_rect_or_endpoints, in_closed_rect in Hebounds.
  change
    ((Rmin (fst (init s)) (fst (term s)) <= fst e <=
       Rmax (fst (init s)) (fst (term s))) /\
     (Rmin (snd (init s)) (snd (term s)) <= snd e <=
       Rmax (snd (init s)) (snd (term s)))) in Hebounds.
  assert (Hvertical :
      snd q < Rmin (snd (init s)) (snd (term s))
      \/ Rmax (snd (init s)) (snd (term s)) < snd q).
  { destruct (Rlt_dec (snd q) (Rmin (snd (init s)) (snd (term s))))
      as [Hbelow | Hbelow]; [now left | right].
    apply Rnot_le_lt. intro Habove.
    apply Hold. split; [exact Hqx |].
    split; [apply Rnot_lt_le in Hbelow; exact Hbelow | exact Habove]. }
  destruct Hvertical as [Hbelow | Habove].
  - assert (Hqe : snd q < snd e) by lra.
    pose proof (proj1 (Hcross e He Hxe) Hqe) as [Hgi Hgt].
    assert (Hqi : snd q < snd (init s)).
    { pose proof (Rmin_l (snd (init s)) (snd (term s))). lra. }
    assert (Hqt : snd q < snd (term s)).
    { pose proof (Rmin_r (snd (init s)) (snd (term s))). lra. }
    pose proof (shift_preserves_strict_vertical_order
                  h q (init s) g gi Hh Hqi Hgi) as Hnewi.
    pose proof (shift_preserves_strict_vertical_order
                  h q (term s) g gt Hh Hqt Hgt) as Hnewt.
    assert (Hnewmin :
      snd (shift h g q) <
      Rmin (snd (shift h gi (init s))) (snd (shift h gt (term s)))).
    { now apply Rmin_glb_lt. }
    exact (Rlt_not_le _ _ Hnewmin (proj1 Hqy)).
  - assert (Heq : snd e < snd q) by lra.
    pose proof (proj2 (Hcross e He Hxe) Heq) as [Hig Htg].
    assert (Hiq : snd (init s) < snd q).
    { pose proof (Rmax_l (snd (init s)) (snd (term s))). lra. }
    assert (Htq : snd (term s) < snd q).
    { pose proof (Rmax_r (snd (init s)) (snd (term s))). lra. }
    pose proof (shift_preserves_strict_vertical_order
                  h (init s) q gi g Hh Hiq Hig) as Hnewi.
    pose proof (shift_preserves_strict_vertical_order
                  h (term s) q gt g Hh Htq Htg) as Hnewt.
    assert (Hnewmax :
      Rmax (snd (shift h gi (init s))) (snd (shift h gt (term s))) <
      snd (shift h g q)).
    { now apply Rmax_lub_lt. }
    exact (Rlt_not_le _ _ Hnewmax (proj2 Hqy)).
Qed.

(* 再接続後の先頭・末尾延長線は、各セグメントの端点長方形を避ける。 *)
Lemma reconnect_preserves_extensions_avoid_rectangles :
  forall ds l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    extensions_avoid_segment_rectangles (ordinary_reconnect_split l sub r h).
Proof.
  intros ds l sub r h Hne Hconn Hmono Hh Hrec Hsparse Hembed Hext.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  unfold extensions_avoid_segment_rectangles.
  intros l' s' r' Hsplit p Hextension Hp.
  assert (Hs' :
    nth_error (ordinary_reconnect_split l sub r h) (length l') = Some s').
  { rewrite Hsplit, nth_error_app2 by lia.
    replace (length l' - length l')%nat with 0%nat by lia.
    reflexivity. }
  assert (Hlen :
    length (l ++ sub ++ r) = length (ordinary_reconnect_split l sub r h)).
  { symmetry. apply ordinary_reconnect_split_length. }
  destruct (nth_error_exists_at_equal_length
              (l ++ sub ++ r) (ordinary_reconnect_split l sub r h)
              (length l') s' Hlen Hs') as [s Hs].
  assert (Hin : In s (l ++ sub ++ r)).
  { now apply nth_error_In in Hs. }
  destruct (@nth_error_split Segment (l ++ sub ++ r) (length l') s Hs)
    as [oldl [oldr [HoldSplit HoldLen]]].
  destruct (Hsparse oldl s oldr HoldSplit) as [HoldExtension _].
  pose proof (ordinary_reconnect_split_nth_spec
                l sub r h (length l') s s'
                Hne Hconn Hmono Hsparse Hwhole (ex_intro _ ds Hembed)
                Hrec Hs Hs')
    as [_ [Hinit Hterm]].
  destruct Hextension as [[Hl' Hhead] | [Hr' Hlast]].
  - destruct (reconnect_head_strict_extension_preimage
                ds l sub r h p Hne Hconn Hmono Hsparse Hembed
                Hext (Rlt_le _ _ (proj1 Hh)) Hhead)
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
               l sub r
               (classify_spec l sub r Hne Hmono Hsparse
                  (ex_intro _ ds Hembed) Hext)
               s e q Hin He Hq Hxe).
    + exact Hp.
  - destruct (reconnect_last_strict_extension_preimage
                ds l sub r h p Hne Hconn Hmono Hsparse Hembed
                Hext (Rlt_le _ _ (proj1 Hh)) Hlast)
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
               l sub r
               (classify_spec l sub r Hne Hmono Hsparse
                  (ex_intro _ ds Hembed) Hext)
               s e q Hin He Hq Hxe).
    + exact Hp.
Qed.

(* 安全な蓋への置換は各位置の端点長方形と外側延長線を変えないので、
   通常再接続版の延長線回避をそのまま安全版へ輸送できる。 *)
Lemma reconnect_split_extensions_avoid_rectangles :
  forall ds l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    extensions_avoid_segment_rectangles (reconnect_split l sub r h).
Proof.
  intros ds l sub r h Hne Hconn Hmono Hh Hsparse Hembed Hext.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { now apply (embed_listDir_connected ds (l ++ sub ++ r)). }
  pose proof (operate_endpoints_reconnectable
                l sub r h Hne Hconn Hmono Hh Hsparse Hwhole
                (ex_intro _ ds Hembed) Hext) as Hrec.
  pose proof (reconnect_preserves_extensions_avoid_rectangles
                ds l sub r h Hne Hconn Hmono Hh Hrec Hsparse Hembed Hext)
    as HordinaryAvoid.
  unfold extensions_avoid_segment_rectangles.
  intros left safe right HsafeSplit p HsafeExt HsafeBox.
  set (safeList := reconnect_split l sub r h).
  set (ordinaryList := ordinary_reconnect_split l sub r h).
  set (oldList := l ++ sub ++ r).
  assert (HsafeNth : nth_error safeList (length left) = Some safe).
  { unfold safeList. rewrite HsafeSplit, nth_error_app2 by lia.
    replace (length left - length left)%nat with 0%nat by lia.
    reflexivity. }
  assert (HordinarySafeLen : length ordinaryList = length safeList).
  { unfold ordinaryList, safeList.
    rewrite ordinary_reconnect_split_length, reconnect_split_safe_length.
    reflexivity. }
  destruct (nth_error_exists_at_equal_length
              ordinaryList safeList (length left) safe
              HordinarySafeLen HsafeNth) as [ordinary HordinaryNth].
  assert (HoldOrdinaryLen : length oldList = length ordinaryList).
  { unfold oldList, ordinaryList. symmetry.
    apply ordinary_reconnect_split_length. }
  destruct (nth_error_exists_at_equal_length
              oldList ordinaryList (length left) ordinary
              HoldOrdinaryLen HordinaryNth) as [old Hold].
  destruct (@nth_error_split Segment ordinaryList (length left)
              ordinary HordinaryNth)
    as [ordinaryLeft [ordinaryRight [HordinarySplit HordinaryLeftLen]]].
  pose proof (ordinary_safe_nth_same_box
                l sub r h (length left) old ordinary safe
                Hne Hconn Hmono Hh Hsparse Hwhole
                (ex_intro _ ds Hembed) Hext Hrec
                Hold HordinaryNth HsafeNth) as [Hbox _].
  apply (HordinaryAvoid ordinaryLeft ordinary ordinaryRight
           HordinarySplit p).
  - destruct HsafeExt as [[Hleft Hhead] | [Hright Hlast]].
    + left. split.
      * intro Hnil. apply Hleft, length_zero_iff_nil.
        rewrite <- HordinaryLeftLen. now rewrite Hnil.
      * apply (proj1 (safe_head_strict_extension_iff_ordinary
                        ds l sub r h p Hne Hconn Hmono Hh Hsparse Hembed Hext)).
        exact Hhead.
    + right. split.
      * intro Hnil. apply Hright, length_zero_iff_nil.
        assert (HsafeLengths :
            (length left + 1 + length right)%nat = length safeList).
        { unfold safeList. rewrite HsafeSplit, !length_app. simpl. lia. }
        assert (HordinaryLengths :
            (length ordinaryLeft + 1 + length ordinaryRight)%nat =
            length ordinaryList).
        { rewrite HordinarySplit, !length_app. simpl. lia. }
        rewrite Hnil in HordinaryLengths. simpl in HordinaryLengths.
        rewrite HordinarySafeLen in HordinaryLengths.
        rewrite HordinaryLeftLen in HordinaryLengths.
        lia.
      * apply (proj1 (safe_last_strict_extension_iff_ordinary
                        ds l sub r h p Hne Hconn Hmono Hh Hsparse Hembed Hext)).
        exact Hlast.
  - apply (same_segment_box_contains safe ordinary p).
    + destruct Hbox as [Hinit Hterm]. split; symmetry; assumption.
    + exact HsafeBox.
Qed.

Definition nonadjacent_bodies_disjoint (ls : list Segment) : Prop :=
  forall i j s t p,
    nth_error ls i = Some s ->
    nth_error ls j = Some t ->
    (S i < j \/ S j < i)%nat ->
    onSegment s p ->
    onSegment t p ->
    False.

(* 全体始点と正パラメータ本体の衝突は、先頭自身なら単射性、直後なら
   dc、それ以降なら非隣接本体非交差で直接排除できる。 *)
Lemma embedded_nonadjacent_initial_point_avoids_positive_body :
  forall ds ls,
    embed_listDir ds ls ->
    nonadjacent_bodies_disjoint ls ->
    forall i s u,
      nth_error ls i = Some s ->
      0 < u <= 1 ->
      init (hd_segment ls) <> point s u.
Proof.
  intros ds ls Hembed Hfar.
  destruct ls as [|first rest].
  { intros i s u Hnth Hu. destruct i; discriminate. }
  intros i s u Hnth Hu.
  destruct i as [|i].
  - simpl in Hnth. injection Hnth as <-.
    intro Heq.
    assert (Hu0 : u = 0).
    { apply (point_injective first).
      change (point first u = init first). now symmetry. }
    lra.
  - destruct i as [|i].
    + destruct rest as [|second rest]; [discriminate |].
      simpl in Hnth. injection Hnth as <-.
      intros Heq.
      destruct Hembed as [sc [_ Hcurve]].
      destruct (embed_scurve_adjacent_data
                  sc (first :: second :: rest) 0 first second
                  Hcurve eq_refl eq_refl)
        as [ps [pt [Hfirst [Hsecond [Hdc Hjoin]]]]].
      assert (HonFirst : onSegment first (init first)) by apply onInit.
      assert (HonSecond : onSegment second (init first)).
      { exists u. split; [lra | now symmetry]. }
      pose proof (adjacent_not_intersect_except_junction
                    ps pt first second (init first)
                    Hdc Hfirst Hsecond Hjoin HonFirst HonSecond) as HeqEnds.
      apply (neq_init_term_y first).
      now apply (f_equal snd) in HeqEnds.
    + intros Heq.
      eapply (Hfar 0%nat (S (S i)) first s (init first)).
      * reflexivity.
      * exact Hnth.
      * left. lia.
      * apply onInit.
      * exists u. split; [lra | now symmetry].
Qed.

(* 長方形回避を実際の本体点へ制限する。先頭自身と末尾自身だけは
   point の単射性で処理し、末尾は t=1 を除く strict 延長線を使う。 *)
Lemma reconnect_split_extensions_avoid_positive_bodies :
  forall ds l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    nonadjacent_bodies_disjoint (reconnect_split l sub r h) ->
    extensions_avoid_positive_bodies (reconnect_split l sub r h).
Proof.
  intros ds l sub r h Hne Hconn Hmono Hh Hsparse Hembed Hext Hfar.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { now apply (embed_listDir_connected ds (l ++ sub ++ r)). }
  assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
  { exact (operate_endpoints_reconnectable
             l sub r h Hne Hconn Hmono Hh Hsparse Hwhole
             (ex_intro _ ds Hembed) Hext). }
  assert (HsafeEmbed : embed_listDir ds (reconnect_split l sub r h)).
  { eapply reconnect_split_safe_preserves_embed; eauto. }
  pose proof (reconnect_split_extensions_avoid_rectangles
                ds l sub r h Hne Hconn Hmono Hh Hsparse Hembed Hext)
    as Havoid.
  unfold extensions_avoid_positive_bodies.
  intros i s u Hnth Hu.
  destruct (@nth_error_split Segment (reconnect_split l sub r h) i s Hnth)
    as [left [right [Hsplit HleftLen]]].
  assert (Hubody : onSegment s (point s u)).
  { exists u. split; [lra | reflexivity]. }
  assert (Hubox : in_rect_or_endpoints_at [s] (point s u)).
  { change (in_segment_rect_or_endpoints s (point s u)).
    now apply segment_in_rect_or_endpoints. }
  split.
  - intros p [v [Hv Hvp]] Heq. subst p.
    destruct (Req_dec v 0) as [-> | Hv0].
    + apply (embedded_nonadjacent_initial_point_avoids_positive_body
               ds (reconnect_split l sub r h) HsafeEmbed Hfar i s u Hnth Hu).
      change (point (hd_segment (reconnect_split l sub r h)) 0 = point s u).
      assumption.
    + assert (Hhead : onHead_extend_strict
                  (reconnect_split l sub r h) (point s u)).
      { exists v. split; [lra | exact Heq]. }
      destruct left as [|a left].
      * simpl in Hsplit.
        assert (Hself : exists v, v < 0 /\ point s v = point s u).
        { unfold onHead_extend_strict in Hhead.
          rewrite Hsplit in Hhead. exact Hhead. }
        destruct Hself as [v' [Hv' Hvu]].
        assert (Huv : u = v').
        { apply (point_injective s). now rewrite Hvu. }
        lra.
      * apply (Havoid (a :: left) s right Hsplit (point s u)).
        -- left. split; [discriminate | exact Hhead].
        -- exact Hubox.
  - intros p Hlast Heq. subst p.
    destruct right as [|a right].
    + assert (HlastEq : last_segment (left ++ [s]) = s).
      { rewrite last_app_nonnil by discriminate. reflexivity. }
      unfold onLast_extend_strict in Hlast.
      rewrite Hsplit, HlastEq in Hlast.
      destruct Hlast as [v [Hv Hvu]].
      assert (Huv : u = v).
      { apply (point_injective s). now rewrite Hvu. }
      lra.
    + apply (Havoid left s (a :: right) Hsplit (point s u)).
      * right. split; [discriminate | exact Hlast].
      * exact Hubox.
Qed.

(* 平行移動後の二つの延長線が交わらない *)
Lemma classified_extension_shifts_disjoint :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    (l <> [] -> reconnect_init_slope_after l sub r h (hd_segment l)) ->
    (r <> [] -> reconnect_term_slope_after l sub r h (last_segment r)) ->
    extensions_disjoint (ordinary_reconnect_split l sub r h).
Proof.
  intros l sub r h Hne Hconn Hmono Hh _ Hsparse Hwhole Hembedded Hdisjoint
    HheadSlope HlastSlope p Hhead Hlast.
  destruct (reconnect_head_extension_preimage
              l sub r h p Hne Hconn Hmono Hsparse Hwhole Hembedded
              Hdisjoint HheadSlope Hhead)
    as [ph [Hph HshiftHead]].
  destruct (reconnect_last_extension_preimage
              l sub r h p Hne Hconn Hmono Hsparse Hwhole Hembedded
              Hdisjoint HlastSlope Hlast)
    as [pl [Hpl HshiftLast]].
  assert (Hx : fst ph = fst pl).
  { assert (HheadX : fst p = fst ph).
    { rewrite HshiftHead, shift_fst. reflexivity. }
    assert (HlastX : fst p = fst pl).
    { rewrite HshiftLast, shift_fst. reflexivity. }
    lra. }
  assert (Hneq : ph <> pl).
  { intro Heq. subst pl. exact (Hdisjoint ph Hph Hpl). }
  pose proof (classified_head_last_extension_order
                l sub r
                (classify_spec l sub r Hne Hmono Hsparse Hembedded Hdisjoint)
                ph pl Hph Hpl Hx) as [HorderHeadLast HorderLastHead].
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

(* 先頭は始点傾き、末尾は終点傾きを保存するため、両延長線を保てる。 *)
Lemma reconnect_preserves_extensions_disjoint :
  forall ds l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    sparse_embedding (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (ordinary_reconnect_split l sub r h).
Proof.
  intros ds l sub r h Hne Hconn Hmono Hh Hrec Hsparse Hext Hembed.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  eapply (classified_extension_shifts_disjoint
            l sub r h Hne Hconn Hmono Hh Hrec Hsparse Hwhole
            (ex_intro _ ds Hembed) Hext).
  - intros Hl. eapply reconnect_head_init_slope_after with (ds := ds); eauto.
    exact (Rlt_le _ _ (proj1 Hh)).
  - intros Hr. eapply reconnect_last_term_slope_after with (ds := ds); eauto.
    exact (Rlt_le _ _ (proj1 Hh)).
Qed.

Definition both_left_of_sub (sub : list Segment) (p q : Point) : Prop :=
  fst p < rx0 (rect_of sub) /\ fst q < rx0 (rect_of sub).

Definition both_right_of_sub (sub : list Segment) (p q : Point) : Prop :=
  rx1 (rect_of sub) < fst p /\ rx1 (rect_of sub) < fst q.

Definition both_above_of_sub (sub : list Segment) (p q : Point) : Prop :=
  ry1 (bbox_of sub) < snd p /\ ry1 (bbox_of sub) < snd q.

Definition both_below_of_sub (sub : list Segment) (p q : Point) : Prop :=
  snd p < ry0 (bbox_of sub) /\ snd q < ry0 (bbox_of sub).

Definition endpoint_box_separated_from_sub
  (sub : list Segment) (p q : Point) : Prop :=
     both_above_of_sub sub p q
  \/ both_below_of_sub sub p q
  \/ both_left_of_sub sub p q
  \/ both_right_of_sub sub p q.

Lemma sub_rect_has_positive_width :
  forall sub,
    sub <> [] -> connected sub -> x_monotone_segs sub ->
    rx0 (rect_of sub) < rx1 (rect_of sub).
Proof.
  intros sub Hne Hconn Hmono.
  pose proof (connected_x_monotone_endpoints sub Hne Hconn Hmono) as Hx.
  unfold rect_of; simpl.
  rewrite Rmin_left, Rmax_right by lra. exact Hx.
Qed.

Lemma segment_rect_has_positive_width :
  forall s, rx0 (rect_of [s]) < rx1 (rect_of [s]).
Proof.
  intros s.
  change (Rmin (fst (init s)) (fst (term s)) <
          Rmax (fst (init s)) (fst (term s))).
  destruct (total_order_T (fst (init s)) (fst (term s)))
    as [[Hlt | Heq] | Hgt].
  - rewrite Rmin_left by lra. rewrite Rmax_right by lra. exact Hlt.
  - exfalso. apply (neq_init_term_x s).
    unfold init_x, term_x. exact Heq.
  - rewrite Rmin_right by lra. rewrite Rmax_left by lra. exact Hgt.
Qed.

(* 二つの閉区間が互いを飛び越していなければ共通点を持つ。 *)
Lemma closed_intervals_have_common_point :
  forall a0 a1 b0 b1,
    a0 <= a1 -> b0 <= b1 -> a0 <= b1 -> b0 <= a1 ->
    exists x, a0 <= x <= a1 /\ b0 <= x <= b1.
Proof.
  intros a0 a1 b0 b1 Ha Hb Hab Hba.
  exists (Rmax a0 b0). split.
  - split; [apply Rmax_l | apply Rmax_lub; assumption].
  - split; [apply Rmax_r | apply Rmax_lub; assumption].
Qed.

(* 左右の同じ側に厳密に固まらない二端点の閉 x 区間は共通する。 *)
Lemma nonhorizontal_sides_have_common_x :
  forall sub s,
    sub <> [] -> connected sub -> x_monotone_segs sub ->
    ~ both_left_of_sub sub (init s) (term s) ->
    ~ both_right_of_sub sub (init s) (term s) ->
    exists x,
      rx0 (rect_of sub) <= x <= rx1 (rect_of sub)
      /\ rx0 (rect_of [s]) <= x <= rx1 (rect_of [s]).
Proof.
  intros sub s Hne Hconn Hmono Hleft Hright.
  pose proof (sub_rect_has_positive_width sub Hne Hconn Hmono) as Hsub.
  pose proof (segment_rect_has_positive_width s) as Hseg.
  assert (HcrossL : rx0 (rect_of sub) <= rx1 (rect_of [s])).
  { apply Rnot_lt_le. intro Hlt. apply Hleft.
    unfold both_left_of_sub, rect_of in *; simpl in *.
    split.
    - eapply Rle_lt_trans; [apply Rmax_l | exact Hlt].
    - eapply Rle_lt_trans; [apply Rmax_r | exact Hlt]. }
  assert (HcrossR : rx0 (rect_of [s]) <= rx1 (rect_of sub)).
  { apply Rnot_lt_le. intro Hlt. apply Hright.
    unfold both_right_of_sub, rect_of in *; simpl in *.
    split.
    - eapply Rlt_le_trans; [exact Hlt | apply Rmin_l].
    - eapply Rlt_le_trans; [exact Hlt | apply Rmin_r]. }
  apply closed_intervals_have_common_point; lra.
Qed.

(* 同じ x の sub 上の点より上を通る非隣接セグメントは、両端とも
   bbox の下端以上にある。 *)
Lemma above_sub_point_bounds_segment_endpoints :
  forall l sub r s p q,
    sparse_embedding (l ++ sub ++ r) ->
    In s (nonadjacent_sides l r) ->
    onSegment s p ->
    onSegmentlist sub q ->
    rx0 (rect_of [s]) <= fst q <= rx1 (rect_of [s]) ->
    snd q < snd p ->
    ry0 (bbox_of sub) <= snd (init s)
    /\ ry0 (bbox_of sub) <= snd (term s).
Proof.
  intros l sub r s p q Hsparse Hs Hp Hq Hqx Hy.
  unfold rect_of in Hqx; simpl in Hqx.
  pose proof (bbox_of_bounds sub q Hq) as [Hqlo _].
  pose proof (segment_in_rect_or_endpoints s p Hp) as Hpbox.
  assert (Hpy : Rmin (snd (init s)) (snd (term s)) <= snd p
                <= Rmax (snd (init s)) (snd (term s))).
  { unfold in_segment_rect_or_endpoints, in_closed_rect in Hpbox.
    change
      ((Rmin (fst (init s)) (fst (term s)) <= fst p <=
          Rmax (fst (init s)) (fst (term s))) /\
       (Rmin (snd (init s)) (snd (term s)) <= snd p <=
          Rmax (snd (init s)) (snd (term s)))) in Hpbox.
    exact (proj2 Hpbox). }
  assert (Havoid := sparse_nonadjacent_box_avoids_sub_points
                       l sub r s q Hsparse Hs Hq).
  split; apply Rnot_lt_le; intro Hend.
  - apply Havoid.
    unfold in_segment_rect_or_endpoints, in_closed_rect, rect_of; simpl.
    split; [lra |].
    destruct Hpy as [Hpy0 Hpy1].
    split.
    + eapply Rle_trans; [apply Rmin_l |].
      eapply Rle_trans; [apply Rlt_le; exact Hend | exact Hqlo].
    + eapply Rle_trans; [apply Rlt_le; exact Hy | exact Hpy1].
  - apply Havoid.
    unfold in_segment_rect_or_endpoints, in_closed_rect, rect_of; simpl.
    split; [lra |].
    destruct Hpy as [Hpy0 Hpy1].
    split.
    + eapply Rle_trans; [apply Rmin_r |].
      eapply Rle_trans; [apply Rlt_le; exact Hend | exact Hqlo].
    + eapply Rle_trans; [apply Rlt_le; exact Hy | exact Hpy1].
Qed.

(* 下側の場合の双対。両端とも bbox の上端以下にある。 *)
Lemma below_sub_point_bounds_segment_endpoints :
  forall l sub r s p q,
    sparse_embedding (l ++ sub ++ r) ->
    In s (nonadjacent_sides l r) ->
    onSegment s p ->
    onSegmentlist sub q ->
    rx0 (rect_of [s]) <= fst q <= rx1 (rect_of [s]) ->
    snd p < snd q ->
    snd (init s) <= ry1 (bbox_of sub)
    /\ snd (term s) <= ry1 (bbox_of sub).
Proof.
  intros l sub r s p q Hsparse Hs Hp Hq Hqx Hy.
  unfold rect_of in Hqx; simpl in Hqx.
  pose proof (bbox_of_bounds sub q Hq) as [_ Hqhi].
  pose proof (segment_in_rect_or_endpoints s p Hp) as Hpbox.
  assert (Hpy : Rmin (snd (init s)) (snd (term s)) <= snd p
                <= Rmax (snd (init s)) (snd (term s))).
  { unfold in_segment_rect_or_endpoints, in_closed_rect in Hpbox.
    change
      ((Rmin (fst (init s)) (fst (term s)) <= fst p <=
          Rmax (fst (init s)) (fst (term s))) /\
       (Rmin (snd (init s)) (snd (term s)) <= snd p <=
          Rmax (snd (init s)) (snd (term s)))) in Hpbox.
    exact (proj2 Hpbox). }
  assert (Havoid := sparse_nonadjacent_box_avoids_sub_points
                       l sub r s q Hsparse Hs Hq).
  split; apply Rnot_lt_le; intro Hend.
  - apply Havoid.
    unfold in_segment_rect_or_endpoints, in_closed_rect, rect_of; simpl.
    split; [lra |].
    destruct Hpy as [Hpy0 Hpy1].
    split.
    + eapply Rle_trans; [exact Hpy0 | apply Rlt_le; exact Hy].
    + eapply Rle_trans; [exact Hqhi |].
      eapply Rle_trans; [apply Rlt_le; exact Hend | apply Rmax_l].
  - apply Havoid.
    unfold in_segment_rect_or_endpoints, in_closed_rect, rect_of; simpl.
    split; [lra |].
    destruct Hpy as [Hpy0 Hpy1].
    split.
    + eapply Rle_trans; [exact Hpy0 | apply Rlt_le; exact Hy].
    + eapply Rle_trans; [exact Hqhi |].
      eapply Rle_trans; [apply Rlt_le; exact Hend | apply Rmax_r].
Qed.

(* x 範囲内の端点には classified_*_bbox を使う。範囲外の端点を
   含む場合は、端点長方形が sub を横切れば sparse に反する。 *)
Lemma operated_nonadjacent_endpoints_separated :
  forall l sub r h s,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    In s (nonadjacent_sides l r) ->
    endpoint_box_separated_from_sub sub
      (operate_point l sub r h (init s))
      (operate_point l sub r h (term s)).
Proof.
  intros l sub r h s Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hs.
  destruct (classic (both_left_of_sub sub (init s) (term s)))
    as [Hleft | Hleft].
  - right; right; left. unfold both_left_of_sub in *.
    now rewrite !operate_point_fst.
  - destruct (classic (both_right_of_sub sub (init s) (term s)))
      as [Hright | Hright].
    + right; right; right. unfold both_right_of_sub in *.
      now rewrite !operate_point_fst.
    + destruct (nonhorizontal_sides_have_common_x
                  sub s Hne Hconn Hmono Hleft Hright)
        as [x [Hsubx Hsegx]].
      destruct (segment_has_point_at_x s x ltac:(lra))
        as [p [Hp Hpx]].
      destruct (x_monotone_sub_has_point sub x Hne Hconn Hmono ltac:(lra))
        as [q [Hq Hqx]].
      assert (Hprange : in_sub_x_range sub p).
      { unfold in_sub_x_range. rewrite Hpx. lra. }
      assert (Hsamex : fst p = fst q) by lra.
      assert (Hpneq : p <> q).
      { intro Heq. subst q.
        apply (sparse_nonadjacent_box_avoids_sub_points
                 l sub r s p Hsparse Hs Hq).
        now apply segment_in_rect_or_endpoints. }
      pose proof (classified_segment_at_sub_x
                    l sub r
                    (classify_spec l sub r Hne Hmono Hsparse Hembedded Hext)
                    s p Hs Hp Hprange) as [Hup Hdown].
      assert (Hy : snd q < snd p \/ snd p < snd q).
      { destruct (total_order_T (snd q) (snd p))
          as [[Hlt | Heq] | Hgt].
        - now left.
        - exfalso. apply Hpneq.
          destruct p as [xp yp], q as [xq yq].
          simpl in Hsamex, Heq |- *. f_equal; lra.
        - now right. }
      assert (Hqsegx :
          rx0 (rect_of [s]) <= fst q <= rx1 (rect_of [s])) by lra.
      destruct Hy as [Hy | Hy].
      * assert (Habove : above_sub_at_x sub p).
        { exists q. repeat split; assumption. }
        destruct (Hup Habove) as [Hinit Hterm].
        pose proof (above_sub_point_bounds_segment_endpoints
                      l sub r s p q Hsparse Hs Hp Hq Hqsegx Hy)
          as [HinitY HtermY].
        left. unfold both_above_of_sub, operate_point, shift.
        rewrite Hinit, Hterm. simpl.
        unfold h_large, rect_height in Hh. lra.
      * assert (Hbelow : below_sub_at_x sub p).
        { exists q. repeat split; assumption. }
        destruct (Hdown Hbelow) as [Hinit Hterm].
        pose proof (below_sub_point_bounds_segment_endpoints
                      l sub r s p q Hsparse Hs Hp Hq Hqsegx Hy)
          as [HinitY HtermY].
        right; left. unfold both_below_of_sub, operate_point, shift.
        rewrite Hinit, Hterm. simpl.
        unfold h_large, rect_height in Hh. lra.
Qed.

Lemma in_rect_or_endpoints_at_closed_bounds :
  forall old p,
    in_rect_or_endpoints_at old p ->
    rx0 (rect_of old) <= fst p <= rx1 (rect_of old)
    /\ ry0 (rect_of old) <= snd p <= ry1 (rect_of old).
Proof.
  intros old p Hp. exact Hp.
Qed.

Lemma in_sub_rect_or_endpoints_bbox_y :
  forall sub p,
    sub <> [] ->
    in_rect_or_endpoints_at sub p ->
    ry0 (bbox_of sub) <= snd p <= ry1 (bbox_of sub).
Proof.
  intros sub p Hne Hp.
  pose proof (bbox_of_bounds sub (init (hd_segment sub))
                (onSegmentlist_init_hd sub Hne)) as Hinit.
  pose proof (bbox_of_bounds sub (term (last_segment sub))
                (onSegmentlist_term_last sub Hne)) as Hterm.
  pose proof (in_rect_or_endpoints_at_closed_bounds sub p Hp) as [_ Hy].
  assert (Hlo : ry0 (bbox_of sub) <= ry0 (rect_of sub)).
  { unfold rect_of; simpl. apply Rmin_glb; lra. }
  assert (Hhi : ry1 (rect_of sub) <= ry1 (bbox_of sub)).
  { unfold rect_of; simpl. apply Rmax_lub; lra. }
  lra.
Qed.

(* 二端点の閉長方形が sub の上下左右のいずれかに厳密に離れていれば、
   その中に収まるセグメントも sub の閉長方形を避ける。 *)
Lemma separated_endpoint_box_avoids_sub :
  forall sub s p,
    sub <> [] ->
    endpoint_box_separated_from_sub sub (init s) (term s) ->
    in_segment_rect_or_endpoints s p ->
    ~ in_rect_or_endpoints_at sub p.
Proof.
  intros sub s p Hne Hsep Hp Hsub.
  pose proof (in_segment_rect_or_endpoints_closed_bounds s p Hp)
    as [[Hpx0 Hpx1] [Hpy0 Hpy1]].
  pose proof (in_sub_rect_or_endpoints_bbox_y sub p Hne Hsub)
    as [Hsy0 Hsy1].
  pose proof (in_rect_or_endpoints_at_closed_bounds sub p Hsub)
    as [[Hsx0 Hsx1] _].
  destruct Hsep as [Habove | [Hbelow | [Hleft | Hright]]].
  - unfold both_above_of_sub in Habove.
    destruct Habove as [Hinit' Hterm'].
    change (Rmin (snd (init s)) (snd (term s)) <= snd p) in Hpy0.
    pose proof (Rmin_glb_lt _ _ _ Hinit' Hterm'). lra.
  - unfold both_below_of_sub in Hbelow.
    destruct Hbelow as [Hinit' Hterm'].
    change (snd p <= Rmax (snd (init s)) (snd (term s))) in Hpy1.
    pose proof (Rmax_lub_lt _ _ _ Hinit' Hterm'). lra.
  - unfold both_left_of_sub in Hleft.
    destruct Hleft as [Hinit' Hterm'].
    change (fst p <= Rmax (fst (init s)) (fst (term s))) in Hpx1.
    pose proof (Rmax_lub_lt _ _ _ Hinit' Hterm'). lra.
  - unfold both_right_of_sub in Hright.
    destruct Hright as [Hinit' Hterm'].
    change (Rmin (fst (init s)) (fst (term s)) <= fst p) in Hpx0.
    pose proof (Rmin_glb_lt _ _ _ Hinit' Hterm'). lra.
Qed.

(* [nonadjacent_sides] に現れるセグメントは、もとの三分割列に属する。 *)
Lemma nonadjacent_sides_in_whole :
  forall l sub r s,
    In s (nonadjacent_sides l r) ->
    In s (l ++ sub ++ r).
Proof.
  intros l sub r s Hs.
  unfold nonadjacent_sides in Hs. rewrite in_app_iff in Hs.
  destruct Hs as [Hl | Hr].
  - rewrite !in_app_iff. left.
    induction l as [|a l IH]; [contradiction|].
    destruct l as [|b l].
    + simpl in Hl. contradiction.
    + simpl in Hl |- *. destruct Hl as [<- | Hl].
      * now left.
      * right. apply IH. exact Hl.
  - rewrite !in_app_iff. right; right.
    destruct r as [|a r]; [simpl in Hr; contradiction|].
    simpl in Hr |- *. now right.
Qed.

(* 非隣接の元セグメントと同じ移動端点を持つ再接続は、形の選び方に
   依らず sub の閉長方形を避ける。蓋用に選び直す場合にも使う。 *)
Lemma reconnected_nonadjacent_avoids_sub_rect :
  forall l sub r h s s',
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    In s (nonadjacent_sides l r) ->
    init s' = operate_point l sub r h (init s) ->
    term s' = operate_point l sub r h (term s) ->
    forall p,
      in_segment_rect_or_endpoints s' p ->
      ~ in_rect_or_endpoints_at sub p.
Proof.
  intros l sub r h s s' Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext
    Hs Hinit Hterm p Hp.
  assert (Hsep : endpoint_box_separated_from_sub sub
      (init s') (term s')).
  { rewrite Hinit, Hterm.
    eapply operated_nonadjacent_endpoints_separated; eauto. }
  apply (separated_endpoint_box_avoids_sub
           sub s' p Hne).
  - exact Hsep.
  - exact Hp.
Qed.

(* 標準の [reconnect_one] は上の一般補題の特別な場合である。 *)
Lemma reconnect_one_avoids_sub_rect :
  forall l sub r h s,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    In s (nonadjacent_sides l r) ->
    forall p,
      in_segment_rect_or_endpoints (reconnect_one l sub r h s) p ->
      ~ in_rect_or_endpoints_at sub p.
Proof.
  intros l sub r h s Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hrec Hs p Hp.
  eapply reconnected_nonadjacent_avoids_sub_rect; eauto.
  - apply reconnect_one_init. apply Hrec.
    now apply nonadjacent_sides_in_whole.
  - apply reconnect_one_term. apply Hrec.
    now apply nonadjacent_sides_in_whole.
Qed.

(* 一セグメント版の退避を、左右の再接続列全体へ持ち上げる。 *)
Lemma reconnect_sides_avoid_sub_rect :
  forall l sub r h s p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    In s (nonadjacent_sides
            (reconnect_segs l sub r h l)
            (reconnect_segs l sub r h r)) ->
    in_segment_rect_or_endpoints s p ->
    ~ in_rect_or_endpoints_at sub p.
Proof.
  intros l sub r h s' p Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext
    Hrec Hs' Hp.
  unfold reconnect_segs in Hs'.
  rewrite nonadjacent_sides_map in Hs'.
  apply in_map_iff in Hs'.
  destruct Hs' as [s [Heq Hs]]. subst s'.
  eapply reconnect_one_avoids_sub_rect; eauto.
Qed.

(* strict 延長線の基点分類と h_large から，移動後の
   延長線点が sub の閉長方形へ入らないことを導く。 *)
Lemma classified_shifted_extension_avoids_sub_rect :
  forall l sub r h p q g,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    (onHead_extend_strict (l ++ sub ++ r) q
     \/ onLast_extend_strict (l ++ sub ++ r) q) ->
    (g = RegUp -> forall z,
      onSegmentlist sub z ->
      fst q = fst z -> snd q < snd z -> classify l sub r z = RegUp) ->
    (g = RegDown -> forall z,
      onSegmentlist sub z ->
      fst q = fst z -> snd z < snd q -> classify l sub r z = RegDown) ->
    (rx0 (rect_of sub) <= fst q <= rx1 (rect_of sub) ->
      g = RegUp \/ g = RegDown) ->
    p = shift h g q ->
    ~ in_rect_or_endpoints_at sub p.
Proof.
  intros l sub r h p q g Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hqextend
    Habove Hbelow Hinside Hshift HpSub.
  pose proof (in_rect_or_endpoints_at_closed_bounds sub p HpSub)
    as [Hpx _].
  pose proof (in_sub_rect_or_endpoints_bbox_y sub p Hne HpSub)
    as Hpy.
  assert (Hxpq : fst p = fst q).
  { rewrite Hshift, shift_fst. reflexivity. }
  destruct (x_monotone_sub_has_point sub (fst p) Hne Hconn Hmono Hpx)
    as [z [Hz Hxz]].
  pose proof (bbox_of_bounds sub z Hz) as Hzy.
  pose proof (classified_sub_fixed
                l sub r
                (classify_spec l sub r Hne Hmono Hsparse Hembedded Hext)
                z Hz) as Hzfix.
  destruct g.
  - simpl in Hshift. subst p.
    destruct (Hinside Hpx); discriminate.
  - assert (Hqz : snd q < snd z).
    { pose proof (f_equal snd Hshift) as Hyshift.
      simpl in Hyshift. unfold h_large, rect_height in Hh. lra. }
    pose proof (Habove eq_refl z Hz ltac:(lra) Hqz) as Hzup.
    congruence.
  - assert (Hzq : snd z < snd q).
    { pose proof (f_equal snd Hshift) as Hyshift.
      simpl in Hyshift. unfold h_large, rect_height in Hh. lra. }
    pose proof (Hbelow eq_refl z Hz ltac:(lra) Hzq) as Hzdown.
    congruence.
Qed.

(* 延長線についても、十分大きな移動後に
   sub の長方形を避ける *)
Lemma reconnect_extensions_avoid_sub_rect :
  forall ds l sub r h p,
    connected (l ++ sub ++ r) ->
    well_split l sub r ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    ((l <> [] /\ onHead_extend_strict (ordinary_reconnect_split l sub r h) p)
     \/ (r <> [] /\ onLast_extend_strict (ordinary_reconnect_split l sub r h) p)) ->
    ~ in_rect_or_endpoints_at sub p.
Proof.
  intros ds l sub r h p Hconn Hws Hh Hsparse Hembed Hext Hextend.
  destruct Hws as [Hne [Hmono _]].
  assert (HconnSub : connected sub).
  { eapply connected_middle. exact Hconn. }
  destruct Hextend as [[Hl Hhead] | [Hr Hlast]].
  - destruct (reconnect_head_strict_extension_preimage
                ds l sub r h p Hne HconnSub Hmono Hsparse Hembed
                Hext (Rlt_le _ _ (proj1 Hh)) Hhead)
      as [q [Hq Hshift]].
    set (g := classify l sub r
                (init (hd_segment (l ++ sub ++ r)))).
    eapply (classified_shifted_extension_avoids_sub_rect
              l sub r h p q g Hne HconnSub Hmono Hh Hsparse Hconn
              (ex_intro _ ds Hembed) Hext).
    + now left.
    + intros Hg z [s [Hs Hz]] Hx Hy. exfalso.
      assert (Hin : In s (l ++ sub ++ r)).
      { rewrite !in_app_iff. right; left; exact Hs. }
      pose proof (proj1
        (classified_head_segment_crossing_order
           l sub r
           (classify_spec l sub r Hne Hmono Hsparse
              (ex_intro _ ds Hembed) Hext)
           s z q Hin Hz Hq ltac:(symmetry; exact Hx)) Hy)
        as [HinitOrder _].
      change
        (classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegUp)
        in Hg.
      rewrite Hg in HinitOrder.
      pose proof (region_at_or_above_RegUp_inv _ HinitOrder) as HinitUp.
      pose proof (classified_sub_fixed
                    l sub r
                    (classify_spec l sub r Hne Hmono Hsparse
                       (ex_intro _ ds Hembed) Hext)
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
           (classify_spec l sub r Hne Hmono Hsparse
              (ex_intro _ ds Hembed) Hext)
           s z q Hin Hz Hq ltac:(symmetry; exact Hx)) Hy)
        as [HinitOrder _].
      change
        (classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegDown)
        in Hg.
      rewrite Hg in HinitOrder.
      pose proof (RegDown_at_or_above_inv _ HinitOrder) as HinitDown.
      pose proof (classified_sub_fixed
                    l sub r
                    (classify_spec l sub r Hne Hmono Hsparse
                       (ex_intro _ ds Hembed) Hext)
                    (init s)
                    ltac:(exists s; split; [exact Hs | apply onInit]))
        as HinitFix.
      congruence.
    + intros Hx.
      exact (classified_head_extension_at_sub_x
               l sub r
               (classify_spec l sub r Hne Hmono Hsparse
                  (ex_intro _ ds Hembed) Hext)
               Hl q Hq Hx).
    + exact Hshift.
  - destruct (reconnect_last_strict_extension_preimage
                ds l sub r h p Hne HconnSub Hmono Hsparse Hembed
                Hext (Rlt_le _ _ (proj1 Hh)) Hlast)
      as [q [Hq Hshift]].
    set (g := classify l sub r
                (term (last_segment (l ++ sub ++ r)))).
    eapply (classified_shifted_extension_avoids_sub_rect
              l sub r h p q g Hne HconnSub Hmono Hh Hsparse Hconn
              (ex_intro _ ds Hembed) Hext).
    + now right.
    + intros Hg z [s [Hs Hz]] Hx Hy. exfalso.
      assert (Hin : In s (l ++ sub ++ r)).
      { rewrite !in_app_iff. right; left; exact Hs. }
      pose proof (proj1
        (classified_last_segment_crossing_order
           l sub r
           (classify_spec l sub r Hne Hmono Hsparse
              (ex_intro _ ds Hembed) Hext)
           s z q Hin Hz Hq ltac:(symmetry; exact Hx)) Hy)
        as [HinitOrder _].
      change
        (classify l sub r (term (last_segment (l ++ sub ++ r))) = RegUp)
        in Hg.
      rewrite Hg in HinitOrder.
      pose proof (region_at_or_above_RegUp_inv _ HinitOrder) as HinitUp.
      pose proof (classified_sub_fixed
                    l sub r
                    (classify_spec l sub r Hne Hmono Hsparse
                       (ex_intro _ ds Hembed) Hext)
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
           (classify_spec l sub r Hne Hmono Hsparse
              (ex_intro _ ds Hembed) Hext)
           s z q Hin Hz Hq ltac:(symmetry; exact Hx)) Hy)
        as [HinitOrder _].
      change
        (classify l sub r (term (last_segment (l ++ sub ++ r))) = RegDown)
        in Hg.
      rewrite Hg in HinitOrder.
      pose proof (RegDown_at_or_above_inv _ HinitOrder) as HinitDown.
      pose proof (classified_sub_fixed
                    l sub r
                    (classify_spec l sub r Hne Hmono Hsparse
                       (ex_intro _ ds Hembed) Hext)
                    (init s)
                    ltac:(exists s; split; [exact Hs | apply onInit]))
        as HinitFix.
      congruence.
    + intros Hx.
      exact (classified_last_extension_at_sub_x
               l sub r
               (classify_spec l sub r Hne Hmono Hsparse
                  (ex_intro _ ds Hembed) Hext)
               Hr q Hq Hx).
    + exact Hshift.
Qed.

(* 全域疎性とは別に、固定した sub 全体の長方形から左右を退避させる。 *)
Lemma reconnect_gives_sparse_around :
  forall ds l sub r h,
    connected (l ++ sub ++ r) ->
    well_split l sub r ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    sparse_around
      (reconnect_segs l sub r h l)
      sub
      (reconnect_segs l sub r h r).
Proof.
  intros ds l sub r h Hconn Hws Hh Hsparse Hembed Hext.
  pose proof Hws as [Hsubne [Hmono _]].
  assert (HconnSub : connected sub).
  { eapply connected_middle. exact Hconn. }
  pose proof (operate_endpoints_reconnectable
                l sub r h Hsubne HconnSub Hmono Hh Hsparse Hconn
                (ex_intro _ ds Hembed) Hext) as Hrec.
  split.
  - intros p Hextend.
    apply (reconnect_extensions_avoid_sub_rect
             ds l sub r h p Hconn Hws Hh Hsparse Hembed Hext).
    destruct Hextend as [[Hl Hhead] | [Hr Hlast]].
    + left. split.
      * intros ->. apply Hl. reflexivity.
      * exact Hhead.
    + right. split.
      * intros ->. apply Hr. reflexivity.
      * exact Hlast.
  - intros s p Hs Hp.
    exact (reconnect_sides_avoid_sub_rect
             l sub r h s p Hsubne HconnSub Hmono Hh
             Hsparse Hconn (ex_intro _ ds Hembed) Hext Hrec Hs Hp).
Qed.

(* 安全な蓋は sub に隣接するため局所 sparse の本体検査から除かれ、
   外側延長線も通常版と一致する。したがって通常版の結論を輸送できる。 *)
Lemma reconnect_gives_safe_sparse_around :
  forall ds l sub r h,
    connected (l ++ sub ++ r) ->
    well_split l sub r ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    sparse_around
      (reconnect_left l sub r h)
      sub
      (reconnect_right l sub r h).
Proof.
  intros ds l sub r h Hwhole Hws Hh Hsparse Hembed Hext.
  pose proof Hws as [Hne [Hmono _]].
  assert (Hconn : connected sub).
  { eapply connected_middle. exact Hwhole. }
  pose proof (reconnect_gives_sparse_around
                ds l sub r h Hwhole Hws Hh Hsparse Hembed Hext)
    as [HordinaryExt HordinaryBody].
  split.
  - intros p [[Hleft Hhead] | [Hright Hlast]].
    + apply HordinaryExt. left. split.
      * intros Hnil. apply Hleft, length_zero_iff_nil.
        rewrite (reconnect_left_length l sub r h).
        rewrite <- (reconnect_segs_length l sub r h l).
        now rewrite Hnil.
      * apply (proj1 (safe_head_strict_extension_iff_ordinary
                        ds l sub r h p Hne Hconn Hmono Hh Hsparse Hembed Hext)).
        exact Hhead.
    + apply HordinaryExt. right. split.
      * intros Hnil. apply Hright, length_zero_iff_nil.
        rewrite (reconnect_right_length l sub r h).
        rewrite <- (reconnect_segs_length l sub r h r).
        now rewrite Hnil.
      * apply (proj1 (safe_last_strict_extension_iff_ordinary
                        ds l sub r h p Hne Hconn Hmono Hh Hsparse Hembed Hext)).
        exact Hlast.
  - intros s p Hs Hp.
    apply (HordinaryBody s p).
    + rewrite <- safe_nonadjacent_sides_eq_ordinary. exact Hs.
    + exact Hp.
Qed.

(* 安全な蓋が外側に現れる singleton の場合にも必要な傾きを保存するため、
   安全版の二延長線は通常版の二延長線と同時に交わる。 *)
Lemma reconnect_split_extensions_disjoint :
  forall ds l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    extensions_disjoint (reconnect_split l sub r h).
Proof.
  intros ds l sub r h Hne Hconn Hmono Hh Hsparse Hembed Hext.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { now apply (embed_listDir_connected ds (l ++ sub ++ r)). }
  pose proof (operate_endpoints_reconnectable
                l sub r h Hne Hconn Hmono Hh Hsparse Hwhole
                (ex_intro _ ds Hembed) Hext) as Hrec.
  pose proof (reconnect_preserves_extensions_disjoint
                ds l sub r h Hne Hconn Hmono Hh Hrec Hsparse Hext Hembed)
    as Hordinary.
  intros p Hhead Hlast.
  apply (Hordinary p).
  - apply (proj1 (safe_head_extension_iff_ordinary
                    ds l sub r h p Hne Hconn Hmono Hh Hsparse Hembed Hext)).
    exact Hhead.
  - apply (proj1 (safe_last_extension_iff_ordinary
                    ds l sub r h p Hne Hconn Hmono Hh Hsparse Hembed Hext)).
    exact Hlast.
Qed.

(* 非隣接な二出現についてだけ要求する本体非交差。隣接の場合は
   PrimitiveSegment の接続規則から別に処理する。 *)
(* 埋め込まれた隣接セグメントは共有接続点でしか交わらず、後続側の
   正パラメータ点はその接続点ではない。 *)
Lemma embedded_adjacent_positive_bodies_disjoint :
  forall ds ls i s t u v,
    embed_listDir ds ls ->
    nth_error ls i = Some s ->
    nth_error ls (S i) = Some t ->
    0 < u <= 1 ->
    0 < v <= 1 ->
    point s u <> point t v.
Proof.
  intros ds ls i s t u v [sc [_ Hembed]] Hs Ht Hu Hv Heq.
  destruct (embed_scurve_adjacent_data sc ls i s t Hembed Hs Ht)
    as [ps [pt [Hsemb [Htemb [Hdc Hjoin]]]]].
  assert (Hons : onSegment s (point s u)).
  { exists u. split; [lra | reflexivity]. }
  assert (Hont : onSegment t (point s u)).
  { exists v. split; [lra | now symmetry]. }
  pose proof (adjacent_not_intersect_except_junction
                ps pt s t (point s u) Hdc Hsemb Htemb Hjoin Hons Hont)
    as Hj.
  assert (Hv0 : v = 0).
  { apply (point_injective t).
    change (point t v = init t).
    rewrite <- Hjoin, <- Hj. now symmetry. }
  lra.
Qed.

(* 非隣接部分を幾何学的に排除できれば、隣接部分は上の補題で補われ、
   全ての異なる出現の正パラメータ本体が非交差になる。 *)
Lemma nonadjacent_and_embedded_give_positive_bodies_disjoint :
  forall ds ls,
    embed_listDir ds ls ->
    nonadjacent_bodies_disjoint ls ->
    positive_bodies_disjoint ls.
Proof.
  intros ds ls Hembed Hfar i j s t u v Hs Ht Hij Hu Hv Heq.
  destruct (Nat.lt_trichotomy i j) as [Hijlt | [-> | Hjilt]].
  - destruct (Nat.eq_dec j (S i)) as [-> | Hnotadj].
    + exact (embedded_adjacent_positive_bodies_disjoint
               ds ls i s t u v Hembed Hs Ht Hu Hv Heq).
    + eapply (Hfar i j s t (point s u)); eauto.
      * left. lia.
      * exists u. split; [lra | reflexivity].
      * exists v. split; [lra | now symmetry].
  - contradiction.
  - destruct (Nat.eq_dec i (S j)) as [-> | Hnotadj].
    + exact (embedded_adjacent_positive_bodies_disjoint
               ds ls j t s v u Hembed Ht Hs Hv Hu (eq_sym Heq)).
    + eapply (Hfar i j s t (point s u)); eauto.
      * right. lia.
      * exists u. split; [lra | reflexivity].
      * exists v. split; [lra | now symmetry].
Qed.

(* open 性に必要な端点の所有規則をここで合成する。全域 sparse は要求せず、
   非隣接本体・strict 延長線・両延長線の三つの非交差だけを使う。 *)
Lemma separated_reconnected_curve_open :
  forall ds ls,
    ls <> [] ->
    embed_listDir ds ls ->
    nonadjacent_bodies_disjoint ls ->
    extensions_avoid_positive_bodies ls ->
    extensions_disjoint ls ->
    ~ close ls.
Proof.
  intros ds ls Hne Hembed Hfar Hextbody Hext.
  apply separated_bodies_extensions_open; [exact Hne | | | exact Hext].
  - now apply (nonadjacent_and_embedded_give_positive_bodies_disjoint ds ls).
  - exact Hextbody.
Qed.
