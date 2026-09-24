Require Export Sparse.ReconnectSeparation.
Require Import Stdlib.Logic.Classical_Prop.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
Open Scope R_scope.
(* 全域 sparse 性は、非隣接セグメントの端点長方形から sub 上の
   任意の点を排除する。 *)
Lemma sparse_nonadjacent_box_avoids_sub_points :
  forall l sub r s q,
    sparse_embedding (l ++ sub ++ r) ->
    In s (nonadjacent_sides l r) ->
    onSegmentlist sub q ->
    ~ in_segment_rect_or_endpoints s q.
Proof.
  intros l sub r s q Hsparse Hs [t [Ht Hqt]] Hqbox.
  destruct (in_app_app sub t Ht) as [sl [sr Hdecomp]].
  assert (Hfull :
      l ++ sub ++ r = (l ++ sl) ++ [t] ++ (sr ++ r)).
  { transitivity (l ++ (sl ++ [t] ++ sr) ++ r).
    - exact (f_equal (fun xs => l ++ xs ++ r) Hdecomp).
    - repeat rewrite app_assoc. reflexivity. }
  pose proof (Hsparse (l ++ sl) t (sr ++ r) Hfull) as Haround.
  assert (Hs' : In s (nonadjacent_sides (l ++ sl) (sr ++ r))).
  { apply nonadjacent_sides_extend_right.
    now apply nonadjacent_sides_extend_left. }
  apply ((proj2 Haround) s q Hs' Hqbox).
  change (in_segment_rect_or_endpoints t q).
  now apply segment_in_rect_or_endpoints.
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
    In s (nonadjacent_sides l r) ->
    endpoint_box_separated_from_sub sub
      (operate_point l sub r h (init s))
      (operate_point l sub r h (term s)).
Proof.
  intros l sub r h s Hne Hconn Hmono Hh Hsparse Hwhole Hs.
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
                    (classify_spec l sub r Hne Hconn Hmono Hsparse Hwhole)
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

(* 再接続した外側セグメントの端点長方形は、十分大きな移動後に
   sub の長方形を避ける。 *)
Lemma reconnect_one_avoids_sub_rect :
  forall l sub r h s,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    In s (nonadjacent_sides l r) ->
    forall p,
      in_segment_rect_or_endpoints (reconnect_one l sub r h s) p ->
      ~ in_rect_or_endpoints_at sub p.
Proof.
  intros l sub r h s Hne Hconn Hmono Hh Hsparse Hwhole Hrec Hs p Hp.
  assert (Hsfull : In s (l ++ sub ++ r)).
  { unfold nonadjacent_sides in Hs. rewrite in_app_iff in Hs.
    destruct Hs as [Hl | Hr].
    - rewrite !in_app_iff. left.
      clear -Hl. induction l as [|a l IH]; [contradiction|].
      destruct l as [|b l].
      + simpl in Hl. contradiction.
      + simpl in Hl |- *. destruct Hl as [<- | Hl].
        * now left.
        * right. apply IH. exact Hl.
    - rewrite !in_app_iff. right; right.
      destruct r as [|a r]; [contradiction|].
      simpl in Hr |- *. now right. }
  assert (HrecOne : reconnectable_after l sub r h s).
  { now apply Hrec. }
  assert (Hsep : endpoint_box_separated_from_sub sub
      (init (reconnect_one l sub r h s))
      (term (reconnect_one l sub r h s))).
  { rewrite (reconnect_one_init l sub r h s HrecOne).
    rewrite (reconnect_one_term l sub r h s HrecOne).
    now apply operated_nonadjacent_endpoints_separated. }
  apply (separated_endpoint_box_avoids_sub
           sub (reconnect_one l sub r h s) p Hne).
  - exact Hsep.
  - exact Hp.
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
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    In s (nonadjacent_sides
            (reconnect_segs l sub r h l)
            (reconnect_segs l sub r h r)) ->
    in_segment_rect_or_endpoints s p ->
    ~ in_rect_or_endpoints_at sub p.
Proof.
  intros l sub r h s' p Hne Hconn Hmono Hh Hsparse Hwhole Hrec Hs' Hp.
  unfold reconnect_segs in Hs'.
  rewrite nonadjacent_sides_map in Hs'.
  apply in_map_iff in Hs'.
  destruct Hs' as [s [Heq Hs]]. subst s'.
  eapply reconnect_one_avoids_sub_rect; eauto.
Qed.

(* sparse 性により，strict 延長線は sub 上の点と一致しない。 *)
Lemma sparse_strict_extension_avoids_sub_point :
  forall l sub r p,
    sparse_embedding (l ++ sub ++ r) ->
    (onHead_extend_strict (l ++ sub ++ r) p
     \/ onLast_extend_strict (l ++ sub ++ r) p) ->
    onSegmentlist sub p ->
    False.
Proof.
  intros l sub r p Hsparse Hextend [s [Hs Hon]].
  apply in_split in Hs.
  destruct Hs as [sub_l [sub_r Hsub]]. subst sub.
  assert (Hwhole :
    l ++ (sub_l ++ s :: sub_r) ++ r =
    (l ++ sub_l) ++ [s] ++ (sub_r ++ r)).
  { repeat rewrite <- app_assoc. simpl. reflexivity. }
  destruct (Hsparse (l ++ sub_l) s (sub_r ++ r) Hwhole)
    as [Havoid _].
  apply (Havoid p).
  - now rewrite <- Hwhole.
  - change (in_segment_rect_or_endpoints s p).
    now apply segment_in_rect_or_endpoints.
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
  intros l sub r h p q g Hne Hconn Hmono Hh Hsparse Hwhole Hqextend
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
                (classify_spec l sub r Hne Hconn Hmono Hsparse Hwhole)
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
    (onHead_extend_strict (reconnect_split l sub r h) p
     \/ onLast_extend_strict (reconnect_split l sub r h) p) ->
    ~ in_rect_or_endpoints_at sub p.
Proof.
  intros ds l sub r h p Hconn Hws Hh Hsparse Hembed Hextend.
  destruct Hws as [Hne [Hmono _]].
  assert (HconnSub : connected sub).
  { eapply connected_middle. exact Hconn. }
  destruct Hextend as [Hhead | Hlast].
  - destruct (reconnect_head_strict_extension_preimage
                ds l sub r h p Hne HconnSub Hmono Hsparse Hembed
                (Rlt_le _ _ (proj1 Hh)) Hhead)
      as [q [Hq Hshift]].
    set (g := classify l sub r
                (init (hd_segment (l ++ sub ++ r)))).
    eapply (classified_shifted_extension_avoids_sub_rect
              l sub r h p q g Hne HconnSub Hmono Hh Hsparse Hconn).
    + now left.
    + intros Hg z [s [Hs Hz]] Hx Hy. exfalso.
      assert (Hin : In s (l ++ sub ++ r)).
      { rewrite !in_app_iff. right; left; exact Hs. }
      pose proof (proj1
        (classified_head_segment_crossing_order
           l sub r
           (classify_spec l sub r Hne HconnSub Hmono Hsparse Hconn)
           s z q Hin Hz Hq ltac:(symmetry; exact Hx)) Hy)
        as [HinitOrder _].
      change
        (classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegUp)
        in Hg.
      rewrite Hg in HinitOrder.
      pose proof (region_at_or_above_RegUp_inv _ HinitOrder) as HinitUp.
      pose proof (classified_sub_fixed
                    l sub r
                    (classify_spec l sub r Hne HconnSub Hmono Hsparse Hconn)
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
           (classify_spec l sub r Hne HconnSub Hmono Hsparse Hconn)
           s z q Hin Hz Hq ltac:(symmetry; exact Hx)) Hy)
        as [HinitOrder _].
      change
        (classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegDown)
        in Hg.
      rewrite Hg in HinitOrder.
      pose proof (RegDown_at_or_above_inv _ HinitOrder) as HinitDown.
      pose proof (classified_sub_fixed
                    l sub r
                    (classify_spec l sub r Hne HconnSub Hmono Hsparse Hconn)
                    (init s)
                    ltac:(exists s; split; [exact Hs | apply onInit]))
        as HinitFix.
      congruence.
    + intros Hx.
      exact (classified_head_extension_at_sub_x
               l sub r
               (classify_spec l sub r Hne HconnSub Hmono Hsparse Hconn)
               q Hq Hx).
    + exact Hshift.
  - destruct (reconnect_last_strict_extension_preimage
                ds l sub r h p Hne HconnSub Hmono Hsparse Hembed
                (Rlt_le _ _ (proj1 Hh)) Hlast)
      as [q [Hq Hshift]].
    set (g := classify l sub r
                (term (last_segment (l ++ sub ++ r)))).
    eapply (classified_shifted_extension_avoids_sub_rect
              l sub r h p q g Hne HconnSub Hmono Hh Hsparse Hconn).
    + now right.
    + intros Hg z [s [Hs Hz]] Hx Hy. exfalso.
      assert (Hin : In s (l ++ sub ++ r)).
      { rewrite !in_app_iff. right; left; exact Hs. }
      pose proof (proj1
        (classified_last_segment_crossing_order
           l sub r
           (classify_spec l sub r Hne HconnSub Hmono Hsparse Hconn)
           s z q Hin Hz Hq ltac:(symmetry; exact Hx)) Hy)
        as [HinitOrder _].
      change
        (classify l sub r (term (last_segment (l ++ sub ++ r))) = RegUp)
        in Hg.
      rewrite Hg in HinitOrder.
      pose proof (region_at_or_above_RegUp_inv _ HinitOrder) as HinitUp.
      pose proof (classified_sub_fixed
                    l sub r
                    (classify_spec l sub r Hne HconnSub Hmono Hsparse Hconn)
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
           (classify_spec l sub r Hne HconnSub Hmono Hsparse Hconn)
           s z q Hin Hz Hq ltac:(symmetry; exact Hx)) Hy)
        as [HinitOrder _].
      change
        (classify l sub r (term (last_segment (l ++ sub ++ r))) = RegDown)
        in Hg.
      rewrite Hg in HinitOrder.
      pose proof (RegDown_at_or_above_inv _ HinitOrder) as HinitDown.
      pose proof (classified_sub_fixed
                    l sub r
                    (classify_spec l sub r Hne HconnSub Hmono Hsparse Hconn)
                    (init s)
                    ltac:(exists s; split; [exact Hs | apply onInit]))
        as HinitFix.
      congruence.
    + intros Hx.
      exact (classified_last_extension_at_sub_x
               l sub r
               (classify_spec l sub r Hne HconnSub Hmono Hsparse Hconn)
               q Hq Hx).
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
    sparse_around
      (reconnect_segs l sub r h l)
      sub
      (reconnect_segs l sub r h r).
Proof.
  intros ds l sub r h Hconn Hws Hh Hsparse Hembed.
  pose proof Hws as [Hsubne [Hmono _]].
  assert (HconnSub : connected sub).
  { eapply connected_middle. exact Hconn. }
  pose proof (operate_endpoints_reconnectable
                l sub r h Hsubne HconnSub Hmono Hh Hsparse Hconn) as Hrec.
  split.
  - intros p Hextend.
    apply (reconnect_extensions_avoid_sub_rect
             ds l sub r h p Hconn Hws Hh Hsparse Hembed).
    exact Hextend.
  - intros s p Hs Hp.
    exact (reconnect_sides_avoid_sub_rect
             l sub r h s p Hsubne HconnSub Hmono Hh
             Hsparse Hconn Hrec Hs Hp).
Qed.

(* 蓋を選び直すと、再接続後の全域 [sparse_embedding] は一般には保たない。
   必要なのは sub 周りの疎性だけであり、それと延長線の非交差から開性を
   保つ。蓋の局所回避を列全体へ合成する補題である。 *)
Lemma reconnect_preserves_open :
  forall ds l sub r h,
    h_large h sub ->
    sub <> [] ->
    x_monotone_segs sub ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    sparse_embedding (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    sparse_around
      (reconnect_segs l sub r h l)
      sub
      (reconnect_segs l sub r h r) ->
    ~ close (l ++ sub ++ r) ->
    ~ close (reconnect_split l sub r h).
Admitted.
