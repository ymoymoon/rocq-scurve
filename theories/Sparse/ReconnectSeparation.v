Require Export Sparse.ReconnectProof.
Require Import Stdlib.Logic.Classical_Prop.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
Open Scope R_scope.

(* ================================================================= *)
(* 疎性と延長線を保つ再接続 *)
(* ================================================================= *)

(* 十分大きい移動では、各セグメントの二端点の y 座標は一致しない。 *)
Lemma operation_height_safe :
  forall l sub r h s,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    In s (l ++ sub ++ r) ->
    snd (operate_point l sub r h (init s)) <>
    snd (operate_point l sub r h (term s)).
Proof.
  intros l sub r h s Hne Hconn Hmono Hh Hsparse Hwhole Hs.
  pose proof (classified_segment_endpoints_monotone
                l sub r
                (classify_spec l sub r Hne Hconn Hmono Hsparse Hwhole)
                s Hs) as [HinitTerm HtermInit].
  destruct (total_order_T (snd (init s)) (snd (term s)))
    as [[Hlt | Heq] | Hgt].
  - pose proof (shift_preserves_strict_vertical_order
                  h (init s) (term s)
                  (classify l sub r (init s))
                  (classify l sub r (term s))
                  (proj1 Hh) Hlt (HinitTerm Hlt)) as Hshift.
    unfold operate_point. lra.
  - exfalso. apply (neq_init_term_y s). exact Heq.
  - pose proof (shift_preserves_strict_vertical_order
                  h (term s) (init s)
                  (classify l sub r (term s))
                  (classify l sub r (init s))
                  (proj1 Hh) Hgt (HtermInit Hgt)) as Hshift.
    unfold operate_point. lra.
Qed.

(* 一つのセグメントについて、分類された両端点を元の向きで再接続できる。 *)
Lemma operate_one_endpoints_reconnectable :
  forall l sub r h s,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    In s (l ++ sub ++ r) ->
    reconnectable_after l sub r h s.
Proof.
  intros l sub r h s Hne Hconn Hmono Hh Hsparse Hwhole Hs.
  unfold reconnectable_after, reconnectable. split.
  - rewrite !operate_point_fst. apply neq_init_term_x.
  - now apply operation_height_safe.
Qed.

Lemma operate_endpoints_reconnectable :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r).
Proof.
  intros l sub r h Hne Hconn Hmono Hh Hsparse Hwhole s Hs.
  now apply (operate_one_endpoints_reconnectable
               l sub r h s Hne Hconn Hmono Hh Hsparse).
Qed.

(* split の同じ位置にある新旧セグメントは向きと operate 後の端点を共有する。 *)
Lemma reconnect_split_nth_spec :
  forall l sub r h i s s',
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (reconnect_split l sub r h) i = Some s' ->
    orn_seg s' = orn_seg s
    /\ init s' = operate_point l sub r h (init s)
    /\ term s' = operate_point l sub r h (term s).
Proof.
  intros l sub r h i s s' Hne Hconn Hmono Hsparse Hwhole Hrec Hold Hnew.
  destruct (Nat.lt_ge_cases i (length l)) as [Hil | Hil].
  - assert (Holdl : nth_error l i = Some s).
    { rewrite <- (nth_error_app1 l (sub ++ r) Hil). exact Hold. }
    assert (Hlenl : length (reconnect_segs l sub r h l) = length l).
    { apply reconnect_segs_length. }
    assert (Hnewl :
        nth_error (reconnect_segs l sub r h l) i = Some s').
    { rewrite <- Hnew. unfold reconnect_split.
      symmetry. apply nth_error_app1. rewrite Hlenl. exact Hil. }
    rewrite (reconnect_segs_nth_error l sub r h l i s Holdl) in Hnewl.
    injection Hnewl as Heq. subst s'.
    assert (Hs : In s (l ++ sub ++ r)).
    { rewrite !in_app_iff. left. now apply nth_error_In in Holdl. }
    split.
    + apply reconnect_one_orn. exact (Hrec s Hs).
    + split.
      * apply reconnect_one_init. exact (Hrec s Hs).
      * apply reconnect_one_term. exact (Hrec s Hs).
  - set (j := (i - length l)%nat).
    assert (Holdtail : nth_error (sub ++ r) j = Some s).
    { unfold j. rewrite <- Hold. symmetry. apply nth_error_app2. lia. }
    assert (Hlenl : length (reconnect_segs l sub r h l) = length l).
    { apply reconnect_segs_length. }
    assert (Hnewtail :
        nth_error (sub ++ reconnect_segs l sub r h r) j = Some s').
    { pose proof Hnew as Hnew'. unfold reconnect_split in Hnew'.
      rewrite nth_error_app2 in Hnew' by (rewrite Hlenl; lia).
      rewrite Hlenl in Hnew'. exact Hnew'. }
    destruct (Nat.lt_ge_cases j (length sub)) as [Hjs | Hjs].
    + assert (Holds : nth_error sub j = Some s).
      { rewrite <- Holdtail. symmetry. apply nth_error_app1. exact Hjs. }
      assert (Hnews : nth_error sub j = Some s').
      { rewrite <- Hnewtail. symmetry. apply nth_error_app1. exact Hjs. }
      rewrite Holds in Hnews. injection Hnews as Heq. subst s'.
      assert (Hins : In s sub) by now apply nth_error_In in Holds.
      repeat split; try reflexivity.
      * symmetry. apply operate_sub_endpoint; try assumption.
        exists s. split; [exact Hins | now left].
      * symmetry. apply operate_sub_endpoint; try assumption.
        exists s. split; [exact Hins | now right].
    + set (k := (j - length sub)%nat).
      assert (Holdr : nth_error r k = Some s).
      { unfold k. rewrite <- Holdtail. symmetry. apply nth_error_app2. lia. }
      assert (Hnewr :
          nth_error (reconnect_segs l sub r h r) k = Some s').
      { unfold k. rewrite <- Hnewtail. symmetry. apply nth_error_app2. lia. }
      rewrite (reconnect_segs_nth_error l sub r h r k s Holdr) in Hnewr.
      injection Hnewr as Heq. subst s'.
      assert (Hs : In s (l ++ sub ++ r)).
      { rewrite !in_app_iff. right. right. now apply nth_error_In in Holdr. }
      split.
      * apply reconnect_one_orn. exact (Hrec s Hs).
      * split.
        -- apply reconnect_one_init. exact (Hrec s Hs).
        -- apply reconnect_one_term. exact (Hrec s Hs).
Qed.

(* 固定した sub との接続点を含め、再接続後も全体が同じ向き列を埋め込む。 *)
Lemma reconnect_split_preserves_embed :
  forall l sub r h ds,
    sub <> [] ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    embed_listDir ds (reconnect_split l sub r h).
Proof.
  intros l sub r h ds Hne Hmono Hsparse Hrec Hembed.
  assert (Hconn : connected sub).
  { apply connected_middle with (l := l) (r := r).
    now apply embed_listDir_connected with (ds := ds). }
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  eapply embed_scurve_transfer; [exact Hembed | | |].
  - unfold reconnect_split. repeat rewrite length_app.
    rewrite !reconnect_segs_length. reflexivity.
  - intros i s s' Hold Hnew.
    exact (proj1 (reconnect_split_nth_spec
                    l sub r h i s s' Hne Hconn Hmono Hsparse Hwhole Hrec
                    Hold Hnew)).
  - intros i s1 s2 H1 H2.
    assert (Hlen :
        length (reconnect_split l sub r h) = length (l ++ sub ++ r)).
    { unfold reconnect_split. repeat rewrite length_app.
      rewrite !reconnect_segs_length. reflexivity. }
    assert (Hi : (i < length (l ++ sub ++ r))%nat).
    { rewrite <- Hlen. now apply nth_error_lt in H1. }
    assert (HSi : (S i < length (l ++ sub ++ r))%nat).
    { rewrite <- Hlen. now apply nth_error_lt in H2. }
    destruct (nth_error (l ++ sub ++ r) i) as [old1 |] eqn:E1.
    2: exfalso; apply (proj2 (nth_error_Some _ _) Hi); exact E1.
    destruct (nth_error (l ++ sub ++ r) (S i)) as [old2 |] eqn:E2.
    2: exfalso; apply (proj2 (nth_error_Some _ _) HSi); exact E2.
    pose proof (reconnect_split_nth_spec
                  l sub r h i old1 s1 Hne Hconn Hmono Hsparse Hwhole Hrec E1 H1)
      as [_ [_ Hterm]].
    pose proof (reconnect_split_nth_spec
                  l sub r h (S i) old2 s2 Hne Hconn Hmono Hsparse Hwhole Hrec E2 H2)
      as [_ [Hinit _]].
    rewrite Hterm, Hinit.
    f_equal. exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed
                      i old1 old2 E1 E2).
Qed.

Lemma reconnect_split_length : forall l sub r h,
  length (reconnect_split l sub r h) = length (l ++ sub ++ r).
Proof.
  intros. unfold reconnect_split. repeat rewrite length_app.
  rewrite !reconnect_segs_length. reflexivity.
Qed.

(* 分割形式の非隣接性を、同じ二つの出現位置を表す添字へ変換する。 *)
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

(*
   廃止した全域 sparse 保存経路。nonadjacent の順序仕様は sub 上の端点を
   比較対象から除くため、この経路の「全端点長方形を分離する」結論は用いない。

   端点間の分類順序により、旧長方形の軸方向の分離は移動後も保たれる。
Lemma operated_endpoint_rectangles_axis_separated :
  forall l sub r h i j s t s' t',
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    0 < h ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (l ++ sub ++ r) j = Some t ->
    (S i < j \/ S j < i)%nat ->
    init s' = operate_point l sub r h (init s) ->
    term s' = operate_point l sub r h (term s) ->
    init t' = operate_point l sub r h (init t) ->
    term t' = operate_point l sub r h (term t) ->
    endpoint_rectangles_axis_separated s t ->
    endpoint_rectangles_axis_separated s' t'.
Proof.
  intros l sub r h i j s t s' t' Hne Hconn Hmono Hsparse Hwhole Hh
    Hs Ht Hfar Hsinit Hsterm Htinit Htterm Haxis.
  assert (Horder :
    forall i0 j0 u v pu pv,
      nth_error (l ++ sub ++ r) i0 = Some u ->
      nth_error (l ++ sub ++ r) j0 = Some v ->
      (S i0 < j0 \/ S j0 < i0)%nat ->
      segment_x_ranges_overlap u v ->
      endpoint_of_seg u pu -> endpoint_of_seg v pv ->
      snd pu < snd pv ->
      snd (operate_point l sub r h pu) <
      snd (operate_point l sub r h pv)).
  { intros i0 j0 u v pu pv Hu Hv Hfar0 Hoverlap Hpu Hpv Hy.
    unfold operate_point. eapply shift_preserves_strict_vertical_order;
      [exact Hh | exact Hy |].
    exact (classified_nonadjacent_endpoint_order
             l sub r
             (classify_spec l sub r Hne Hconn Hmono Hsparse Hwhole)
             i0 j0 u v pu pv Hu Hv Hfar0 Hoverlap Hpu Hpv
             (Rlt_le _ _ Hy)). }
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
         now left | now left |].
      apply Hold; now left.
    * eapply (Horder j i t s (init t) (term s));
        [exact Ht | exact Hs | exact Hfar' | exact Hoverlap' |
         now left | now right |].
      apply Hold; [now left | now right].
    * eapply (Horder j i t s (term t) (init s));
        [exact Ht | exact Hs | exact Hfar' | exact Hoverlap' |
         now right | now left |].
      apply Hold; [now right | now left].
    * eapply (Horder j i t s (term t) (term s));
        [exact Ht | exact Hs | exact Hfar' | exact Hoverlap' |
         now right | now right |].
      apply Hold; now right.
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
         now left | now left |].
      apply Hold; now left.
    * eapply (Horder i j s t (init s) (term t));
        [exact Hs | exact Ht | exact Hfar | exact Hoverlap |
         now left | now right |].
      apply Hold; [now left | now right].
    * eapply (Horder i j s t (term s) (init t));
        [exact Hs | exact Ht | exact Hfar | exact Hoverlap |
         now right | now left |].
      apply Hold; [now right | now left].
    * eapply (Horder i j s t (term s) (term t));
        [exact Hs | exact Ht | exact Hfar | exact Hoverlap |
         now right | now right |].
      apply Hold; now right.
Qed.

(* 再接続後の異なるセグメントの端点長方形も互いを避ける。 *)
Lemma reconnect_preserves_segment_rectangles_separated :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    segment_rectangles_separated (reconnect_split l sub r h).
Proof.
  intros l sub r h Hne Hconn Hmono Hh Hrec Hsparse Hwhole.
  unfold segment_rectangles_separated.
  intros l' s' r' Hsplit t' Ht' p Hp.
  destruct (split_nonadjacent_nth_errors
              (reconnect_split l sub r h) l' s' r' t' Hsplit Ht')
    as [i [j [Hs' [Ht'idx Hfar]]]].
  assert (Hlen :
    length (l ++ sub ++ r) = length (reconnect_split l sub r h)).
  { symmetry. apply reconnect_split_length. }
  destruct (nth_error_exists_at_equal_length
              (l ++ sub ++ r) (reconnect_split l sub r h) i s' Hlen Hs')
    as [s Hs].
  destruct (nth_error_exists_at_equal_length
              (l ++ sub ++ r) (reconnect_split l sub r h) j t' Hlen Ht'idx)
    as [t Ht].
  pose proof (reconnect_split_nth_spec
                l sub r h i s s' Hne Hconn Hmono Hsparse Hwhole Hrec Hs Hs')
    as [_ [Hsinit Hsterm]].
  pose proof (reconnect_split_nth_spec
                l sub r h j t t' Hne Hconn Hmono Hsparse Hwhole Hrec Ht Ht'idx)
    as [_ [Htinit Htterm]].
  destruct (nth_error_far_in_nonadjacent_sides
              (l ++ sub ++ r) i j s t Hs Ht Hfar)
    as [l0 [r0 [HoldSplit HoldIn]]].
  destruct (Hsparse l0 s r0 HoldSplit) as [_ HoldRect].
  assert (HoldAxis : endpoint_rectangles_axis_separated s t).
  { apply rectangles_avoid_implies_axis_separated.
    intros q Hq. exact (HoldRect t q HoldIn Hq). }
  assert (HnewAxis : endpoint_rectangles_axis_separated s' t').
  { eapply (operated_endpoint_rectangles_axis_separated
              l sub r h i j s t s' t');
      [exact Hne | exact Hconn | exact Hmono | exact Hsparse |
       exact Hwhole | exact (proj1 Hh) | exact Hs | exact Ht | exact Hfar |
       exact Hsinit | exact Hsterm | exact Htinit | exact Htterm |
       exact HoldAxis]. }
  exact (axis_separated_boxes_avoid s' t' HnewAxis p Hp).
Qed.

*)

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
    extensions_avoid_segment_rectangles (reconnect_split l sub r h).
Proof.
  intros ds l sub r h Hne Hconn Hmono Hh Hrec Hsparse Hembed.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  unfold extensions_avoid_segment_rectangles.
  intros l' s' r' Hsplit p Hextension Hp.
  assert (Hs' :
    nth_error (reconnect_split l sub r h) (length l') = Some s').
  { rewrite Hsplit, nth_error_app2 by lia.
    replace (length l' - length l')%nat with 0%nat by lia.
    reflexivity. }
  assert (Hlen :
    length (l ++ sub ++ r) = length (reconnect_split l sub r h)).
  { symmetry. apply reconnect_split_length. }
  destruct (nth_error_exists_at_equal_length
              (l ++ sub ++ r) (reconnect_split l sub r h)
              (length l') s' Hlen Hs') as [s Hs].
  assert (Hin : In s (l ++ sub ++ r)).
  { now apply nth_error_In in Hs. }
  destruct (@nth_error_split Segment (l ++ sub ++ r) (length l') s Hs)
    as [oldl [oldr [HoldSplit _]]].
  destruct (Hsparse oldl s oldr HoldSplit) as [HoldExtension _].
  pose proof (reconnect_split_nth_spec
                l sub r h (length l') s s'
                Hne Hconn Hmono Hsparse Hwhole Hrec Hs Hs')
    as [_ [Hinit Hterm]].
  destruct Hextension as [Hhead | Hlast].
  - destruct (reconnect_head_strict_extension_preimage
                ds l sub r h p Hne Hconn Hmono Hsparse Hembed
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
    + apply (HoldExtension q). left.
      change (onHead_extend_strict (oldl ++ s :: oldr) q).
      now rewrite <- HoldSplit.
    + intros e He Hxe.
      exact (classified_head_segment_crossing_order
               l sub r
               (classify_spec l sub r Hne Hconn Hmono Hsparse Hwhole)
               s e q Hin He Hq Hxe).
    + exact Hp.
  - destruct (reconnect_last_strict_extension_preimage
                ds l sub r h p Hne Hconn Hmono Hsparse Hembed
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
    + apply (HoldExtension q). right.
      change (onLast_extend_strict (oldl ++ s :: oldr) q).
      now rewrite <- HoldSplit.
    + intros e He Hxe.
      exact (classified_last_segment_crossing_order
               l sub r
               (classify_spec l sub r Hne Hconn Hmono Hsparse Hwhole)
               s e q Hin He Hq Hxe).
    + exact Hp.
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
    extensions_disjoint (l ++ sub ++ r) ->
    (l <> [] -> reconnect_init_slope_after l sub r h (hd_segment l)) ->
    (r <> [] -> reconnect_term_slope_after l sub r h (last_segment r)) ->
    extensions_disjoint (reconnect_split l sub r h).
Proof.
  intros l sub r h Hne Hconn Hmono Hh _ Hsparse Hwhole Hdisjoint
    HheadSlope HlastSlope p Hhead Hlast.
  destruct (reconnect_head_extension_preimage
              l sub r h p Hne Hconn Hmono Hsparse Hwhole HheadSlope Hhead)
    as [ph [Hph HshiftHead]].
  destruct (reconnect_last_extension_preimage
              l sub r h p Hne Hconn Hmono Hsparse Hwhole HlastSlope Hlast)
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
                (classify_spec l sub r Hne Hconn Hmono Hsparse Hwhole)
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
    extensions_disjoint (reconnect_split l sub r h).
Proof.
  intros ds l sub r h Hne Hconn Hmono Hh Hrec Hsparse Hext Hembed.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  apply classified_extension_shifts_disjoint; try assumption.
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
