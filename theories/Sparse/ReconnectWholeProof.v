Require Export Sparse.ReconnectLocalProof.
From Stdlib Require Import Lra Lia Psatz.
Import ListNotations.

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

Lemma nth_error_decompose : forall (xs : list Segment) i seg,
  nth_error xs i = Some seg ->
  exists a b, xs = a ++ [seg] ++ b /\ length a = i.
Proof.
  induction xs as [|s tail IH]; intros [|i] seg H; simpl in H; try discriminate.
  - inversion H; subst. exists [],tail. auto.
  - destruct (IH i seg H) as [a [b [E Ha]]].
    exists (s::a),b. split; [simpl; now rewrite E | simpl; lia].
Qed.

Lemma sparse_triangles_at_indices : forall ls i j s t,
  sparse_embedding ls -> nth_error ls i = Some s -> nth_error ls j = Some t ->
  (S i < j \/ S j < i)%nat ->
  forall p, in_segment_triangle s p -> ~ in_segment_triangle t p.
Proof.
  intros ls i j s t Hsparse Hs Ht Hfar.
  destruct (nth_error_far_in_nonadjacent_sides ls i j s t Hs Ht Hfar)
    as [a [b [He Hin]]].
  intros p Hsp Htp. exact ((proj2 (Hsparse a s b He)) t p Hin Htp Hsp).
Qed.

Lemma sparse_extension_at_index : forall ls which i seg p,
  sparse_embedding ls -> nth_error ls i = Some seg ->
  other_than_end which ls i -> on_strict_extension which ls p ->
  ~ in_segment_triangle seg p.
Proof.
  intros ls which i seg p Hsparse Hi Ho Hp.
  destruct (nth_error_decompose ls i seg Hi) as [a [b [He Ha]]].
  apply (proj1 (Hsparse a seg b He)).
  destruct which; simpl in Ho,Hp.
  - left. split; [intro E; subst a; simpl in Ha; lia | exact Hp].
  - right. split; [|exact Hp].
    intro E. subst b. apply Ho. rewrite He, length_app. simpl.
    rewrite Ha. lia.
Qed.

Lemma separated_fibres_order : forall s t x,
  segment_x_range s x -> segment_x_range t x ->
  (forall p, in_segment_triangle s p -> ~ in_segment_triangle t p) ->
  triangle_upper s x < triangle_lower t x \/
  triangle_upper t x < triangle_lower s x.
Proof.
  intros s t x Hsx Htx Hdis.
  pose proof (triangle_bounds_ordered s x Hsx).
  pose proof (triangle_bounds_ordered t x Htx).
  destruct (Rlt_dec (triangle_upper s x) (triangle_lower t x)); [now left |].
  destruct (Rlt_dec (triangle_upper t x) (triangle_lower s x)); [now right |].
  exfalso.
  destruct (Rle_dec (triangle_lower s x) (triangle_lower t x)).
  - apply (Hdis (x,triangle_lower t x)); apply in_triangle_iff_fibre; split; try assumption; lra.
  - apply (Hdis (x,triangle_lower s x)); apply in_triangle_iff_fibre; split; try assumption; lra.
Qed.

Lemma classified_fibre_order : forall l sub r k i j s t x,
  ClassificationSpec l sub r k ->
  nth_error (l ++ sub ++ r) i = Some s ->
  nth_error (l ++ sub ++ r) j = Some t ->
  (S i < j \/ S j < i)%nat ->
  In s (l ++ r) -> In t (l ++ r) ->
  segment_x_range s x -> segment_x_range t x ->
  triangle_upper s x < triangle_lower t x ->
  upper_displacement k s x <= lower_displacement k t x.
Proof.
  intros l sub r k i j s t x Hspec Hs Ht Hfar Hsi Hti Hsx Htx Hgap.
  destruct (segment_point_at_x s x Hsx) as [ys [Hys Bys]].
  destruct (segment_point_at_x t x Htx) as [yt [Hyt Byt]].
  exact (classified_external_segment_order _ _ _ _ Hspec i j s t (x,ys) (x,yt)
    Hs Ht Hfar Hsi Hti Hys Hyt eq_refl ltac:(simpl; lra)).
Qed.

(* S2 と補間恒等式により、外側二三角形の隙間は縮まらない。 *)
Lemma reconnected_external_triangles_disjoint : forall l sub r k h i j s t s' t',
  ClassificationSpec l sub r k -> sparse_embedding (l ++ sub ++ r) ->
  0 <= h ->
  nth_error (l ++ sub ++ r) i = Some s ->
  nth_error (l ++ sub ++ r) j = Some t ->
  (S i < j \/ S j < i)%nat ->
  In s (l ++ r) -> In t (l ++ r) ->
  reconnect_segment (scale_classifier h k) s s' ->
  reconnect_segment (scale_classifier h k) t t' ->
  forall p, in_segment_triangle s' p -> ~ in_segment_triangle t' p.
Proof.
  intros l sub r k h i j s t s' t' Hspec Hsparse Hh Hs Ht Hfar Hsi Hti Hrs Hrt
    [x y] Hps Hpt.
  apply in_triangle_iff_fibre in Hps,Hpt.
  destruct Hps as [Hsx Hsy]. destruct Hpt as [Htx Hty].
  apply (proj1 (reconnect_x_range _ _ _ _ Hrs)) in Hsx.
  apply (proj1 (reconnect_x_range _ _ _ _ Hrt)) in Htx.
  destruct (reconnect_boundary_values _ _ _ x Hrs) as [Ls Us].
  destruct (reconnect_boundary_values _ _ _ x Hrt) as [Lt Ut].
  rewrite Ls,Us,lower_value_scale,upper_value_scale in Hsy.
  rewrite Lt,Ut,lower_value_scale,upper_value_scale in Hty.
  destruct (separated_fibres_order s t x Hsx Htx
    (sparse_triangles_at_indices _ _ _ _ _ Hsparse Hs Ht Hfar)) as [Hgap | Hgap].
  - pose proof (classified_fibre_order _ _ _ _ _ _ _ _ _ Hspec Hs Ht Hfar Hsi Hti Hsx Htx Hgap).
    unfold lower_displacement,upper_displacement in *. nra.
  - assert (Hrev : (S j < i \/ S i < j)%nat) by tauto.
    pose proof (classified_fibre_order _ _ _ _ _ _ _ _ _ Hspec Ht Hs Hrev Hti Hsi Htx Hsx Hgap).
    unfold lower_displacement,upper_displacement in *. nra.
Qed.

(* S3 は sub を含む全ての本体との順序を保存する。 *)
Lemma shifted_extension_avoids_reconnected_triangle :
  forall l sub r k h which i seg seg' q,
  ClassificationSpec l sub r k -> sparse_embedding (l ++ sub ++ r) -> 0 <= h ->
  nth_error (l ++ sub ++ r) i = Some seg ->
  other_than_end which (l ++ sub ++ r) i ->
  on_strict_extension which (l ++ sub ++ r) q ->
  reconnect_segment (scale_classifier h k) seg seg' ->
  ~ in_segment_triangle seg'
      (translate_pt (0,h*k (extension_anchor which (l ++ sub ++ r))) q).
Proof.
  intros l sub r k h which i seg seg' [x y] Hspec Hsparse Hh Hi Ho Hq Hr Hnew.
  apply in_triangle_iff_fibre in Hnew.
  unfold translate_pt in Hnew. simpl in Hnew. rewrite Rplus_0_r in Hnew.
  destruct Hnew as [Hx Hy].
  apply (proj1 (reconnect_x_range _ _ _ _ Hr)) in Hx.
  destruct (reconnect_boundary_values _ _ _ x Hr) as [Hl Hu].
  rewrite Hl,Hu,lower_value_scale,upper_value_scale in Hy.
  pose proof (sparse_extension_at_index _ _ _ _ _ Hsparse Hi Ho Hq) as Hout.
  destruct (segment_point_at_x seg x Hx) as [z [Hz Bz]].
  destruct (classified_extension_segment_order _ _ _ _ Hspec
    which i seg (x,z) (x,y) Hi Ho Hz Hq eq_refl) as [Hbelow Habove].
  destruct (Rlt_dec y (triangle_lower seg x)).
  - specialize (Hbelow ltac:(simpl; lra)). simpl in Hbelow.
    unfold lower_displacement in Hbelow. nra.
  - assert (Hupper : triangle_upper seg x < y).
    { destruct (Rlt_dec (triangle_upper seg x) y); [assumption |].
      exfalso. apply Hout. apply in_triangle_iff_fibre; split; [exact Hx | lra]. }
    specialize (Habove ltac:(simpl; lra)). simpl in Habove.
    unfold upper_displacement in Habove. nra.
Qed.

Lemma reconnect_preserves_extensions_disjoint : forall l sub r k h l' r',
  PreparedGeometry l sub r -> ClassificationSpec l sub r k ->
  extensions_disjoint (l ++ sub ++ r) -> 0 <= h ->
  reconnect_split (scale_classifier h k) l sub r l' r' ->
  extensions_disjoint (l' ++ sub ++ r').
Proof.
  intros l sub r k h l' r' Hgeom Hspec Hext Hh Hr p Hhp Hlp.
  pose proof (prepared_sub_nonempty _ _ _ Hgeom) as Hne.
  pose proof (scale_sub_fixed _ _ _ _ h Hspec) as Hfix.
  destruct (reconnect_whole_extension_preimage _ _ _ _ _ _ HeadEnd p
    Hne Hfix Hr Hhp) as [[xh yh] [Hhead Eh]].
  destruct (reconnect_whole_extension_preimage _ _ _ _ _ _ LastEnd p
    Hne Hfix Hr Hlp) as [[xl yl] [Hlast El]].
  assert (Hx : xh=xl).
  { apply (f_equal fst) in Eh,El. unfold translate_pt in Eh,El. simpl in *; lra. }
  subst xl.
  assert (Hyn : yh<>yl).
  { intro E. subst yl. exact (Hext _ Hhead Hlast). }
  destruct (classified_head_last_extension_order _ _ _ _ Hspec
    (xh,yh) (xh,yl) Hhead Hlast eq_refl) as [Hhl Hlh].
  apply (f_equal snd) in Eh,El.
  unfold translate_pt,scale_classifier,extension_anchor in Eh,El; simpl in Eh,El.
  destruct (Rlt_dec yh yl).
  - specialize (Hhl ltac:(simpl; lra)). simpl in Hhl. nra.
  - specialize (Hlh ltac:(simpl; lra)). simpl in Hlh. nra.
Qed.

Lemma sub_nth_other_than_end : forall l sub r which i seg,
  external_end_nonempty which l r -> nth_error sub i = Some seg ->
  nth_error (l ++ sub ++ r) (length l+i) = Some seg /\
  other_than_end which (l ++ sub ++ r) (length l+i).
Proof.
  intros l sub r which i seg Hend Hi.
  assert (Hlt : (i<length sub)%nat) by (eapply nth_error_lt; eassumption).
  split.
  - rewrite nth_error_app2 by lia.
    replace (length l+i-length l)%nat with i by lia.
    rewrite nth_error_app1 by exact Hlt. exact Hi.
  - destruct which; simpl in *.
    + destruct l; [contradiction | simpl; lia].
    + rewrite !length_app. destruct r; [contradiction | simpl; lia].
Qed.

Lemma classified_extension_sub_order : forall l sub r k which q e,
  ClassificationSpec l sub r k -> sparse_embedding (l ++ sub ++ r) ->
  external_end_nonempty which l r ->
  on_strict_extension which (l ++ sub ++ r) q ->
  onSegmentlist sub e -> fst q=fst e ->
  (0<k (extension_anchor which (l ++ sub ++ r)) -> snd e<snd q) /\
  (k (extension_anchor which (l ++ sub ++ r))<0 -> snd q<snd e).
Proof.
  intros l sub r k which [x y] [xe ye] Hspec Hsparse Hend Hq [seg [Hin He]] Hx.
  simpl in Hx. subst xe.
  destruct (In_nth_error sub seg Hin) as [i Hi].
  destruct (sub_nth_other_than_end l sub r which i seg Hend Hi) as [Hnth Hother].
  pose proof (sparse_extension_at_index _ _ _ _ _ Hsparse Hnth Hother Hq) as Hout.
  assert (Hneq : y<>ye).
  { intro E. subst ye. apply Hout. now apply segment_in_endpoint_triangle. }
  destruct (classified_extension_segment_order _ _ _ _ Hspec which
    (length l+i)%nat seg (x,ye) (x,y) Hnth Hother He Hq eq_refl) as [Hbelow Habove].
  destruct (sub_boundary_values_zero _ _ _ _ seg x Hspec Hin) as [Hlow Hup].
  simpl in Hbelow,Habove. rewrite Hlow in Hbelow. rewrite Hup in Habove.
  split; intros Hd; simpl in *.
  - destruct (Rlt_dec y ye) as [Hlt | Hnlt]; [specialize (Hbelow Hlt); lra | lra].
  - destruct (Rlt_dec ye y) as [Hlt | Hnlt]; [specialize (Habove Hlt); lra | lra].
Qed.

(* S3 と S6 により、同じ倍率で延長線全体も閉長方形から退避する。 *)
Lemma classified_extension_eventually_escapes : forall l sub r k which,
  PreparedGeometry l sub r -> ClassificationSpec l sub r k ->
  sparse_embedding (l ++ sub ++ r) ->
  (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
  external_end_nonempty which l r ->
  exists h0, 0<=h0 /\ forall h, h0<=h ->
    forall q, on_strict_extension which (l ++ sub ++ r) q ->
      ~ in_rect_or_endpoints_at sub
        (translate_pt (0,h*k (extension_anchor which (l ++ sub ++ r))) q).
Proof.
  intros l sub r k which Hgeom Hspec Hsparse [ds Hembed] Hend.
  set (d := k (extension_anchor which (l ++ sub ++ r))).
  assert (Hreference : forall x y,
    on_strict_extension which (l ++ sub ++ r) (x,y) ->
    in_sub_x_range sub (x,0) ->
    exists z, ry0 (rect_of sub)<=z<=ry1 (rect_of sub) /\
      (0<d -> z<y) /\ (d<0 -> y<z)).
  { intros x y Hq Hx.
    assert (Hconn : connected sub).
    { exact (connected_middle l sub r (embed_listDir_connected ds _ Hembed)). }
    destruct (connected_sub_has_point_at_x sub x
      (prepared_sub_nonempty _ _ _ Hgeom) Hconn Hx)
      as [[a z] [Hz Hax]].
    simpl in Hax. subst a.
    pose proof (prepared_sub_contained _ _ _ Hgeom (x,z) Hz) as Hbounds.
    destruct Hbounds as [_ Hy].
    exists z. split; [exact Hy |].
    exact (classified_extension_sub_order l sub r k which (x,y) (x,z)
      Hspec Hsparse Hend Hq Hz eq_refl). }
  destruct (Rlt_dec 0 d) as [Hpos | Hnpos].
  - destruct (eventually_above (ry0 (rect_of sub)) d (ry1 (rect_of sub))
      ltac:(lra) ltac:(lra)) as [a [Ha Hthreshold]].
    exists a. split; [exact Ha |]. intros h Hh [x y] Hq Hrect.
    unfold in_rect_or_endpoints_at,in_closed_rect,translate_pt in Hrect.
    simpl in Hrect. rewrite Rplus_0_r in Hrect. fold d in Hrect.
    destruct Hrect as [Hx Hy].
    destruct (Hreference x y Hq Hx) as [z [Hz [Hzy _]]].
    specialize (Hzy Hpos). specialize (Hthreshold h Hh).
    simpl in Hz,Hthreshold. lra.
  - destruct (Rlt_dec d 0) as [Hneg | Hnneg].
    + destruct (eventually_above (-ry1 (rect_of sub)) (-d) (-ry0 (rect_of sub))
        ltac:(lra) ltac:(lra)) as [a [Ha Hthreshold]].
      exists a. split; [exact Ha |]. intros h Hh [x y] Hq Hrect.
      unfold in_rect_or_endpoints_at,in_closed_rect,translate_pt in Hrect.
      simpl in Hrect. rewrite Rplus_0_r in Hrect. fold d in Hrect.
      destruct Hrect as [Hx Hy].
      destruct (Hreference x y Hq Hx) as [z [Hz [_ Hzy]]].
      specialize (Hzy Hneg). specialize (Hthreshold h Hh).
      simpl in Hz,Hthreshold. nra.
    + assert (Hz : d=0) by lra.
      exists 0. split; [lra |]. intros h Hh [x y] Hq Hrect.
      apply (classified_fixed_extension_clear _ _ _ _ Hspec which Hend Hz (x,y) Hq).
      unfold translate_pt in Hrect. simpl in Hrect. fold d in Hrect.
      rewrite Hz in Hrect.
      replace (x+0,y+h*0) with (x,y) in Hrect by (f_equal; ring).
      exact Hrect.
Qed.

Lemma classified_extensions_eventually_escape : forall l sub r k,
  PreparedGeometry l sub r -> ClassificationSpec l sub r k ->
  sparse_embedding (l ++ sub ++ r) ->
  (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
  exists h0, 0<=h0 /\ forall h, h0<=h ->
    forall which, external_end_nonempty which l r ->
    forall q, on_strict_extension which (l ++ sub ++ r) q ->
      ~ in_rect_or_endpoints_at sub
        (translate_pt (0,h*k (extension_anchor which (l ++ sub ++ r))) q).
Proof.
  intros l sub r k Hgeom Hspec Hsparse Hembed.
  assert (Hlocal : forall which, exists a, 0<=a /\ forall h, a<=h ->
    external_end_nonempty which l r ->
    forall q, on_strict_extension which (l ++ sub ++ r) q ->
    ~ in_rect_or_endpoints_at sub
      (translate_pt (0,h*k (extension_anchor which (l ++ sub ++ r))) q)).
  { intros which. destruct which.
    - destruct l as [|a tail].
      + exists 0. split; [lra | intros h Hh H; contradiction].
      + destruct (classified_extension_eventually_escapes _ _ _ _ HeadEnd
          Hgeom Hspec Hsparse Hembed ltac:(discriminate)) as [b [Hb Hclear]].
        exists b. split; [exact Hb | intros h Hh _; exact (Hclear h Hh)].
    - destruct r as [|a tail].
      + exists 0. split; [lra | intros h Hh H; contradiction].
      + destruct (classified_extension_eventually_escapes _ _ _ _ LastEnd
          Hgeom Hspec Hsparse Hembed ltac:(discriminate)) as [b [Hb Hclear]].
        exists b. split; [exact Hb | intros h Hh _; exact (Hclear h Hh)]. }
  destruct (finite_eventual_bound CurveEnd [HeadEnd;LastEnd]
    (fun which h => external_end_nonempty which l r ->
      forall q, on_strict_extension which (l ++ sub ++ r) q ->
      ~ in_rect_or_endpoints_at sub
        (translate_pt (0,h*k (extension_anchor which (l ++ sub ++ r))) q))
    ltac:(intros which Hin; exact (Hlocal which)))
    as [b [Hb Hclear]].
  exists b. split; [exact Hb |]. intros h Hh which.
  apply (Hclear h Hh which). destruct which; simpl; auto.
Qed.

Lemma first_segment_y_direction : forall sub v h c,
  sub<>[] -> sub_contained_in_endpoint_rect sub ->
  embed (v,h,c) (hd_segment sub) ->
  match v with
  | n => snd (init (hd_segment sub))<snd (term (last_segment sub))
  | s => snd (term (last_segment sub))<snd (init (hd_segment sub))
  end.
Proof.
  intros [|a tail] v h c Hne Hcontained He; [contradiction |].
  pose proof (Hcontained (term a) ltac:(exists a; split; [now left | apply onTerm])) as [_ Hy].
  change (Rmin (snd (init a)) (snd (term (last_segment (a::tail))))<=snd (term a)<=
          Rmax (snd (init a)) (snd (term (last_segment (a::tail))))) in Hy.
  destruct v.
  - pose proof (n_end_relation a h c He).
    unfold Rmin,Rmax in Hy; destruct Rle_dec; simpl; lra.
  - pose proof (s_end_relation a h c He).
    unfold Rmin,Rmax in Hy; destruct Rle_dec; simpl; lra.
Qed.

Lemma last_segment_y_direction : forall sub v h c,
  sub<>[] -> sub_contained_in_endpoint_rect sub ->
  embed (v,h,c) (last_segment sub) ->
  match v with
  | n => snd (init (hd_segment sub))<snd (term (last_segment sub))
  | s => snd (term (last_segment sub))<snd (init (hd_segment sub))
  end.
Proof.
  intros sub v h c Hne Hcontained He.
  pose proof (Hcontained (init (last_segment sub))
    ltac:(exists (last_segment sub); split; [now apply last_In | apply onInit])) as [_ Hy].
  change (Rmin (snd (init (hd_segment sub))) (snd (term (last_segment sub)))<=
      snd (init (last_segment sub))<=
      Rmax (snd (init (hd_segment sub))) (snd (term (last_segment sub)))) in Hy.
  destruct v.
  - pose proof (n_end_relation _ h c He).
    unfold Rmin,Rmax in Hy; destruct Rle_dec; simpl; lra.
  - pose proof (s_end_relation _ h c He).
    unfold Rmin,Rmax in Hy; destruct Rle_dec; simpl; lra.
Qed.

Lemma adjacent_split_data : forall ds xs ys,
  embed_listDir ds (xs++ys) -> xs<>[] -> ys<>[] ->
  exists p q, embed p (last_segment xs) /\ embed q (hd_segment ys) /\
    dc p q /\ term (last_segment xs)=init (hd_segment ys).
Proof.
  intros ds xs ys [sc [Hdir Hemb]] Hxs Hys.
  assert (Hpos : (0<length xs)%nat) by (destruct xs; [contradiction | simpl; lia]).
  assert (Hi : nth_error (xs++ys) (length xs-1)=Some (last_segment xs)).
  { rewrite nth_error_app1 by lia. apply nth_error_last. exact Hxs. }
  assert (Hj : nth_error (xs++ys) (S (length xs-1))=Some (hd_segment ys)).
  { replace (S (length xs-1)) with (length xs) by lia.
    rewrite nth_error_app2 by lia.
    replace (length xs-length xs)%nat with 0%nat by lia.
    destruct ys; [contradiction | reflexivity]. }
  exact (embed_scurve_adjacent_data sc _ _ _ _ Hemb Hi Hj).
Qed.

(* 先頭の四つの型と dc から、左隣接三角形と端点長方形の接触は共有端点に限る。 *)
Lemma incoming_boundary_only_touches_sub : forall ds l sub r p,
  PreparedGeometry l sub r -> embed_listDir ds (l++sub++r) -> l<>[] ->
  in_segment_triangle (last_segment l) p -> in_rect_or_endpoints_at sub p ->
  p=init (hd_segment sub).
Proof.
  intros ds l sub r p Hgeom Hembed Hl Hp Hrect.
  pose proof (prepared_sub_nonempty _ _ _ Hgeom) as Hsub.
  assert (Htail : sub++r<>[]) by (intro E; apply app_eq_nil in E; tauto).
  destruct (adjacent_split_data ds l (sub++r) Hembed Hl Htail)
    as [a [b [Ha [Hb [Hdc Hj]]]]].
  assert (Hhd : hd_segment (sub++r)=hd_segment sub).
  { destruct sub; [contradiction | reflexivity]. }
  rewrite Hhd in Hb,Hj.
  assert (Hconn : connected sub).
  { apply (connected_middle l sub r). now apply (embed_listDir_connected ds). }
  pose proof (connected_x_monotone_endpoints sub Hsub Hconn
    (prepared_sub_x_monotone _ _ _ Hgeom)) as Hxorder.
  assert (Hmono : x_monotone_seg (hd_segment sub)).
  { apply (prepared_sub_x_monotone _ _ _ Hgeom).
    destruct sub; [contradiction | now left]. }
  destruct b as [[v hor] c].
  assert (Hhor : hor=e).
  { destruct hor; [reflexivity |].
    pose proof (w_end_relation _ v c Hb).
    unfold x_monotone_seg,init_x,term_x in Hmono. lra. }
  subst hor.
  pose proof (first_segment_y_direction sub v e c Hsub
    (prepared_sub_contained _ _ _ Hgeom) Hb) as Hyorder.
  destruct Hrect as [Hx Hy].
  change (Rmin (fst (init (hd_segment sub))) (fst (term (last_segment sub)))<=fst p<=
          Rmax (fst (init (hd_segment sub))) (fst (term (last_segment sub)))) in Hx.
  change (Rmin (snd (init (hd_segment sub))) (snd (term (last_segment sub)))<=snd p<=
          Rmax (snd (init (hd_segment sub))) (snd (term (last_segment sub)))) in Hy.
  rewrite Rmin_left,Rmax_right in Hx by lra.
  destruct v.
  -
    rewrite Rmin_left,Rmax_right in Hy by lra.
    destruct (dc_predecessor_north_east c a Hdc) as [[hor ->] | [-> | ->]].
    + assert (Hpc : primitive_segment (last_segment l)=(n,hor,cc)).
      { eapply embed_unique; [apply primitive_segment_embed | exact Ha]. }
      rewrite <-Hj. eapply triangle_exposed_endpoint; [now right | exact Hp |].
      left. split; [now rewrite Hpc |]. split.
      * unfold high_value. rewrite Hpc. simpl. rewrite Hj. lra.
      * unfold high_value. rewrite Hpc. reflexivity.
    + rewrite <-Hj. apply east_triangle_exposed_term; [now left | exact Hp |].
      unfold term_x. rewrite Hj. lra.
    + rewrite <-Hj. apply east_triangle_exposed_term; [now right | exact Hp |].
      unfold term_x. rewrite Hj. lra.
  -
    rewrite Rmin_right,Rmax_left in Hy by lra.
    destruct (dc_predecessor_south_east c a Hdc) as [[hor ->] | [-> | ->]].
    + assert (Hpc : primitive_segment (last_segment l)=(s,hor,cx)).
      { eapply embed_unique; [apply primitive_segment_embed | exact Ha]. }
      rewrite <-Hj. eapply triangle_exposed_endpoint; [now right | exact Hp |].
      right. split; [now rewrite Hpc |]. split.
      * unfold low_value. rewrite Hpc. simpl. rewrite Hj. lra.
      * unfold low_value. rewrite Hpc. reflexivity.
    + rewrite <-Hj. apply east_triangle_exposed_term; [now left | exact Hp |].
      unfold term_x. rewrite Hj. lra.
    + rewrite <-Hj. apply east_triangle_exposed_term; [now right | exact Hp |].
      unfold term_x. rewrite Hj. lra.
Qed.

Lemma outgoing_boundary_only_touches_sub : forall ds l sub r p,
  PreparedGeometry l sub r -> embed_listDir ds (l++sub++r) -> r<>[] ->
  in_segment_triangle (hd_segment r) p -> in_rect_or_endpoints_at sub p ->
  p=term (last_segment sub).
Proof.
  intros ds l sub r p Hgeom Hembed Hr Hp Hrect.
  pose proof (prepared_sub_nonempty _ _ _ Hgeom) as Hsub.
  assert (Hprefix : l++sub<>[]) by (intro E; apply app_eq_nil in E; tauto).
  rewrite app_assoc in Hembed.
  destruct (adjacent_split_data ds (l++sub) r Hembed Hprefix Hr)
    as [a [b [Ha [Hb [Hdc Hj]]]]].
  rewrite last_app_nonnil in Ha,Hj by exact Hsub.
  assert (Hconn : connected sub).
  { apply (connected_middle l sub r).
    apply (embed_listDir_connected ds). now rewrite app_assoc. }
  pose proof (connected_x_monotone_endpoints sub Hsub Hconn
    (prepared_sub_x_monotone _ _ _ Hgeom)) as Hxorder.
  assert (Hmono : x_monotone_seg (last_segment sub)).
  { apply (prepared_sub_x_monotone _ _ _ Hgeom). now apply last_In. }
  destruct a as [[v hor] c].
  assert (Hhor : hor=e).
  { destruct hor; [reflexivity |].
    pose proof (w_end_relation _ v c Ha).
    unfold x_monotone_seg,init_x,term_x in Hmono. lra. }
  subst hor.
  pose proof (last_segment_y_direction sub v e c Hsub
    (prepared_sub_contained _ _ _ Hgeom) Ha) as Hyorder.
  destruct Hrect as [Hx Hy].
  change (Rmin (fst (init (hd_segment sub))) (fst (term (last_segment sub)))<=fst p<=
          Rmax (fst (init (hd_segment sub))) (fst (term (last_segment sub)))) in Hx.
  change (Rmin (snd (init (hd_segment sub))) (snd (term (last_segment sub)))<=snd p<=
          Rmax (snd (init (hd_segment sub))) (snd (term (last_segment sub)))) in Hy.
  rewrite Rmin_left,Rmax_right in Hx by lra.
  destruct v.
  -
    rewrite Rmin_left,Rmax_right in Hy by lra.
    destruct (dc_successor_north_east c b Hdc) as [[hor ->] | [-> | ->]].
    + assert (Hpc : primitive_segment (hd_segment r)=(n,hor,cx)).
      { eapply embed_unique; [apply primitive_segment_embed | exact Hb]. }
      rewrite Hj. eapply triangle_exposed_endpoint; [now left | exact Hp |].
      right. split; [now rewrite Hpc |]. split.
      * unfold low_value. rewrite Hpc. simpl. rewrite <-Hj. lra.
      * unfold low_value. rewrite Hpc. reflexivity.
    + rewrite Hj. apply east_triangle_exposed_init; [now left | exact Hp |].
      unfold init_x. rewrite <-Hj. lra.
    + rewrite Hj. apply east_triangle_exposed_init; [now right | exact Hp |].
      unfold init_x. rewrite <-Hj. lra.
  -
    rewrite Rmin_right,Rmax_left in Hy by lra.
    destruct (dc_successor_south_east c b Hdc) as [[hor ->] | [-> | ->]].
    + assert (Hpc : primitive_segment (hd_segment r)=(s,hor,cc)).
      { eapply embed_unique; [apply primitive_segment_embed | exact Hb]. }
      rewrite Hj. eapply triangle_exposed_endpoint; [now left | exact Hp |].
      left. split; [now rewrite Hpc |]. split.
      * unfold high_value. rewrite Hpc. simpl. rewrite <-Hj. lra.
      * unfold high_value. rewrite Hpc. reflexivity.
    + rewrite Hj. apply east_triangle_exposed_init; [now right | exact Hp |].
      unfold init_x. rewrite <-Hj. lra.
    + rewrite Hj. apply east_triangle_exposed_init; [now left | exact Hp |].
      unfold init_x. rewrite <-Hj. lra.
Qed.
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


Lemma reconnect_nth_sub : forall d l sub r l' r' i seg,
  reconnect_split d l sub r l' r' -> nth_error sub i=Some seg ->
  nth_error (l'++sub++r') (length l+i)=Some seg.
Proof.
  intros d l sub r l' r' i seg Hr Hi.
  pose proof (reconnect_list_length _ _ _ (reconnect_left _ _ _ _ _ _ Hr)) as Hlen.
  rewrite nth_error_app2 by lia.
  replace (length l+i-length l')%nat with i by lia.
  rewrite nth_error_app1; [exact Hi | eapply nth_error_lt; exact Hi].
Qed.

Lemma reconnected_side_avoids_sub_triangle :
  forall ds l sub r k h l' r' i j s s' t p,
  PreparedGeometry l sub r -> ClassificationSpec l sub r k ->
  embed_listDir ds (l++sub++r) ->
  embed_listDir ds (l'++sub++r') ->
  reconnect_split (scale_classifier h k) l sub r l' r' ->
  (forall seg, In seg (nonadjacent_sides l r) ->
    triangle_escapes_sub (scale_classifier h k) sub seg) ->
  nth_error (l++sub++r) i=Some s -> nth_error (l'++sub++r') i=Some s' ->
  reconnect_segment (scale_classifier h k) s s' ->
  nth_error sub j=Some t ->
  (S i<length l+j \/ S (length l+j)<i)%nat ->
  ((i<length l)%nat \/ (length l+length sub<=i)%nat) ->
  in_segment_triangle s' p -> in_segment_triangle t p -> False.
Proof.
  intros ds l sub r k h l' r' i j s s' t p Hgeom Hspec Hembed Hnew Hr Hclear
    Hi Hi' Hrec Hj Hfar Hout Hp Ht.
  pose proof (prepared_sub_nonempty _ _ _ Hgeom) as Hne.
  pose proof (prepared_sub_x_monotone _ _ _ Hgeom) as Hmono.
  assert (Hconn : connected sub) by
    (apply (connected_middle l sub r); exact (embed_listDir_connected ds _ Hembed)).
  pose proof (contained_sub_triangle sub t p (prepared_sub_contained _ _ _ Hgeom)
    (nth_error_In _ _ Hj) Ht) as HK.
  pose proof (prepared_geometry_transport l sub r l' r' Hgeom) as Hgeom'.
  pose proof (reconnect_list_length _ _ _ (reconnect_left _ _ _ _ _ _ Hr)) as Hllen.
  pose proof (reconnect_list_length _ _ _ (reconnect_right _ _ _ _ _ _ Hr)) as Hrlen.
  destruct Hout as [Hleft | Hright].
  - assert (Hlocal : nth_error l i=Some s) by (now rewrite nth_error_app1 in Hi).
    destruct (Nat.lt_ge_cases (S i) (length l)) as [Hinterior | Hboundary].
    + apply (reconnected_triangle_avoids_sub (scale_classifier h k) sub s s' p Hrec); try assumption.
      apply Hclear. unfold nonadjacent_sides. apply in_or_app. left.
      eapply nth_before_last_in_removelast; eassumption.
    + assert (Hidx : i=(length l-1)%nat) by lia.
      assert (Hl' : l'<>[]) by (intro E; subst l'; simpl in Hllen; lia).
      assert (Hlast : s'=last_segment l').
      { rewrite nth_error_app1 in Hi' by lia.
        pose proof (@nth_error_last Segment l' default_segment Hl') as HH.
        assert (Ei : i=(length l'-1)%nat) by lia.
        rewrite <-Ei,Hi' in HH. inversion HH. reflexivity. }
      rewrite Hlast in Hp.
      pose proof (incoming_boundary_only_touches_sub ds l' sub r' p
        Hgeom' Hnew Hl' Hp HK) as Ep.
      pose proof (proj1 (inner_sub_x_bounds sub j t Hne Hconn Hmono Hj)
        ltac:(lia)) as Hstrict.
      destruct Ht as [[Hpx Hpy] Hc].
      change (Rmin (init_x t) (term_x t)<=fst p<=Rmax (init_x t) (term_x t)) in Hpx.
      pose proof (Hmono t (nth_error_In _ _ Hj)) as Hmt.
      unfold x_monotone_seg in Hmt.
      rewrite Rmin_left,Rmax_right in Hpx by lra.
      rewrite Ep in Hpx. lra.
  - assert (Hlocal : nth_error r (i-length l-length sub)=Some s).
    { rewrite nth_error_app2 in Hi by lia. now rewrite nth_error_app2 in Hi by lia. }
    destruct (Nat.eq_dec (i-length l-length sub) 0) as [Hboundary | Hinterior].
    + assert (Hr' : r'<>[]).
      { intro E. subst r'. simpl in Hrlen.
        destruct r; [rewrite Hboundary in Hlocal; discriminate | simpl in Hrlen; lia]. }
      assert (Hfirst : s'=hd_segment r').
      { rewrite nth_error_app2 in Hi' by lia.
        rewrite nth_error_app2 in Hi' by lia.
        replace (i-length l'-length sub)%nat with 0%nat in Hi' by lia.
        destruct r'; [contradiction | simpl in Hi'; inversion Hi'; reflexivity]. }
      rewrite Hfirst in Hp.
      pose proof (outgoing_boundary_only_touches_sub ds l' sub r' p
        Hgeom' Hnew Hr' Hp HK) as Ep.
      assert (Hjt : (j<length sub)%nat) by (eapply nth_error_lt; eassumption).
      pose proof (proj2 (inner_sub_x_bounds sub j t Hne Hconn Hmono Hj)
        ltac:(lia)) as Hstrict.
      destruct Ht as [[Hpx Hpy] Hc].
      change (Rmin (init_x t) (term_x t)<=fst p<=Rmax (init_x t) (term_x t)) in Hpx.
      pose proof (Hmono t (nth_error_In _ _ Hj)) as Hmt.
      unfold x_monotone_seg in Hmt.
      rewrite Rmin_left,Rmax_right in Hpx by lra.
      rewrite Ep in Hpx. lra.
    + apply (reconnected_triangle_avoids_sub (scale_classifier h k) sub s s' p Hrec); try assumption.
      apply Hclear. unfold nonadjacent_sides. apply in_or_app. right.
      destruct r as [|a tail]; [destruct (i-length l-length sub)%nat; discriminate |].
      destruct (i-length l-length sub)%nat as [|z] eqn:E; [contradiction |].
      simpl in Hlocal. now apply nth_error_In in Hlocal.
Qed.

Lemma nth_at_split : forall (a b : list Segment) seg,
  nth_error (a++[seg]++b) (length a)=Some seg.
Proof.
  intros. rewrite nth_error_app2 by lia.
  replace (length a-length a)%nat with 0%nat by lia. reflexivity.
Qed.

(* 固定 sub、外側二三角形、遠い退避部分、隣接境界の四場合で分離する。 *)
Lemma reconnect_preserves_triangle_separation :
  forall ds l sub r k h l' r',
  PreparedGeometry l sub r -> ClassificationSpec l sub r k ->
  sparse_embedding (l++sub++r) -> embed_listDir ds (l++sub++r) -> 0<=h ->
  reconnect_split (scale_classifier h k) l sub r l' r' ->
  (forall seg, In seg (nonadjacent_sides l r) ->
    triangle_escapes_sub (scale_classifier h k) sub seg) ->
  segment_triangles_separated (l'++sub++r').
Proof.
  intros ds l sub r k h l' r' Hgeom Hspec Hsparse Hembed Hh Hr Hclear.
  pose proof (reconnect_whole_list _ _ _ _ _ _ (scale_sub_fixed _ _ _ _ h Hspec) Hr) as Hrel.
  pose proof (reconnect_list_embed _ _ _ _ Hrel Hembed) as Hnew.
  intros a s' b Hsplit t' p Hin Htp Hsp.
  destruct (split_nonadjacent_nth_errors _ _ _ _ _ Hsplit Hin)
    as [i [j [Hi' [Hj' Hfar]]]].
  destruct (reconnect_nth_old _ _ _ _ _ Hrel Hi') as [s [Hi Hrs]].
  destruct (reconnect_nth_old _ _ _ _ _ Hrel Hj') as [t [Hj Hrt]].
  destruct (nth_sub_or_sides l sub r i s Hi) as [[z [Ei Hzi]] | [HoutS Hsin]];
  destruct (nth_sub_or_sides l sub r j t Hj) as [[w [Ej Hwj]] | [HoutT Htin]].
  - pose proof (reconnect_nth_sub _ _ _ _ _ _ _ _ Hr Hzi) as Hsi.
    pose proof (reconnect_nth_sub _ _ _ _ _ _ _ _ Hr Hwj) as Htj.
    rewrite <-Ei,Hi' in Hsi. rewrite <-Ej,Hj' in Htj.
    inversion Hsi; inversion Htj; subst s' t'.
    exact (sparse_triangles_at_indices _ _ _ _ _ Hsparse Hi Hj Hfar p Hsp Htp).
  - pose proof (reconnect_nth_sub _ _ _ _ _ _ _ _ Hr Hzi) as Hsi.
    rewrite <-Ei,Hi' in Hsi. inversion Hsi; subst s'.
    exact (reconnected_side_avoids_sub_triangle ds l sub r k h l' r' j z t t' s p
      Hgeom Hspec Hembed Hnew Hr Hclear Hj Hj' Hrt Hzi ltac:(lia) HoutT Htp Hsp).
  - pose proof (reconnect_nth_sub _ _ _ _ _ _ _ _ Hr Hwj) as Htj.
    rewrite <-Ej,Hj' in Htj. inversion Htj; subst t'.
    exact (reconnected_side_avoids_sub_triangle ds l sub r k h l' r' i w s s' t p
      Hgeom Hspec Hembed Hnew Hr Hclear Hi Hi' Hrs Hwj ltac:(lia) HoutS Hsp Htp).
  - exact (reconnected_external_triangles_disjoint l sub r k h i j s t s' t'
      Hspec Hsparse Hh Hi Hj Hfar Hsin Htin Hrs Hrt p Hsp Htp).
Qed.

Lemma reconnect_preserves_extension_avoidance : forall l sub r k h l' r',
  PreparedGeometry l sub r -> ClassificationSpec l sub r k ->
  sparse_embedding (l++sub++r) -> 0<=h ->
  reconnect_split (scale_classifier h k) l sub r l' r' ->
  extensions_avoid_segment_triangles (l'++sub++r').
Proof.
  intros l sub r k h l' r' Hgeom Hspec Hsparse Hh Hr.
  pose proof (prepared_sub_nonempty _ _ _ Hgeom) as Hne.
  pose proof (scale_sub_fixed _ _ _ _ h Hspec) as Hfix.
  pose proof (reconnect_whole_list _ _ _ _ _ _ Hfix Hr) as Hrel.
  pose proof (reconnect_list_length _ _ _ Hrel) as Hlen.
  intros a s' b Hsplit p Hext Hp.
  assert (Hi' : nth_error (l'++sub++r') (length a)=Some s').
  { rewrite Hsplit. apply nth_at_split. }
  destruct (reconnect_nth_old _ _ _ _ _ Hrel Hi') as [s [Hi Hrec]].
  destruct Hext as [[Hprefix Hhead] | [Hsuffix Hlast]].
  - assert (Hother : other_than_end HeadEnd (l++sub++r) (length a)).
    { simpl. destruct a; [contradiction | simpl; lia]. }
    destruct (reconnect_whole_strict_extension_preimage _ _ _ _ _ _ HeadEnd p
      Hne Hfix Hr Hhead) as [q [Hq Eq]].
    rewrite Eq in Hp.
    exact (shifted_extension_avoids_reconnected_triangle l sub r k h HeadEnd (length a) s s' q
      Hspec Hsparse Hh Hi Hother Hq Hrec Hp).
  - assert (Hother : other_than_end LastEnd (l++sub++r) (length a)).
    { simpl. rewrite Hlen,Hsplit,!length_app. simpl.
      destruct b; [contradiction | simpl; lia]. }
    destruct (reconnect_whole_strict_extension_preimage _ _ _ _ _ _ LastEnd p
      Hne Hfix Hr Hlast) as [q [Hq Eq]].
    rewrite Eq in Hp.
    exact (shifted_extension_avoids_reconnected_triangle l sub r k h LastEnd (length a) s s' q
      Hspec Hsparse Hh Hi Hother Hq Hrec Hp).
Qed.

Lemma reconnect_preserves_sparse : forall ds l sub r k h l' r',
  PreparedGeometry l sub r -> ClassificationSpec l sub r k ->
  sparse_embedding (l++sub++r) -> embed_listDir ds (l++sub++r) -> 0<=h ->
  reconnect_split (scale_classifier h k) l sub r l' r' ->
  (forall seg, In seg (nonadjacent_sides l r) ->
    triangle_escapes_sub (scale_classifier h k) sub seg) ->
  sparse_embedding (l'++sub++r').
Proof.
  intros. apply geometric_triangle_sparse_embedding.
  - eapply reconnect_preserves_triangle_separation; eassumption.
  - eapply reconnect_preserves_extension_avoidance; eassumption.
Qed.

Lemma reconnect_removelast : forall d xs ys,
  reconnect_list d xs ys -> reconnect_list d (removelast xs) (removelast ys).
Proof.
  intros d xs ys Hr. induction Hr as [|x y xs ys Hxy Hrel IH].
  - constructor.
  - destruct xs as [|a xs],ys as [|b ys].
    + constructor.
    + inversion Hrel.
    + inversion Hrel.
    + change (reconnect_list d (x::removelast (a::xs)) (y::removelast (b::ys))).
      constructor; assumption.
Qed.

Lemma reconnect_tl : forall d xs ys,
  reconnect_list d xs ys -> reconnect_list d (tl xs) (tl ys).
Proof. intros d xs ys Hr. destruct Hr; simpl; [constructor | assumption]. Qed.

Lemma reconnect_in_old : forall d xs ys y,
  reconnect_list d xs ys -> In y ys ->
  exists x, In x xs /\ reconnect_segment d x y.
Proof.
  intros d xs ys y Hr Hy. destruct (In_nth_error ys y Hy) as [i Hi].
  destruct (reconnect_nth_old _ _ _ _ _ Hr Hi) as [x [Hx Hrec]].
  exists x. split; [now apply nth_error_In in Hx | exact Hrec].
Qed.

Lemma reconnect_gives_sparse_around : forall l sub r k h l' r',
  PreparedGeometry l sub r -> ClassificationSpec l sub r k ->
  reconnect_split (scale_classifier h k) l sub r l' r' ->
  (forall seg, In seg (nonadjacent_sides l r) ->
    triangle_escapes_sub (scale_classifier h k) sub seg) ->
  (forall which, external_end_nonempty which l r ->
    forall q, on_strict_extension which (l++sub++r) q ->
      ~ in_rect_or_endpoints_at sub
        (translate_pt (0,h*k (extension_anchor which (l++sub++r))) q)) ->
  sparse_around l' sub r'.
Proof.
  intros l sub r k h l' r' Hgeom Hspec Hr Htri Hext.
  pose proof (prepared_sub_nonempty _ _ _ Hgeom) as Hne.
  pose proof (scale_sub_fixed _ _ _ _ h Hspec) as Hfix.
  split.
  - intros p [[Hl Hhead] | [Hrr Hlast]] HK.
    + assert (Hln : l<>[]).
      { intro E. pose proof (reconnect_left _ _ _ _ _ _ Hr) as Hrel.
        rewrite E in Hrel. inversion Hrel; subst. contradiction. }
      destruct (reconnect_whole_strict_extension_preimage _ _ _ _ _ _ HeadEnd p
        Hne Hfix Hr Hhead) as [q [Hq Eq]].
      rewrite Eq in HK. exact (Hext HeadEnd Hln q Hq HK).
    + assert (Hrn : r<>[]).
      { intro E. pose proof (reconnect_right _ _ _ _ _ _ Hr) as Hrel.
        rewrite E in Hrel. inversion Hrel; subst. contradiction. }
      destruct (reconnect_whole_strict_extension_preimage _ _ _ _ _ _ LastEnd p
        Hne Hfix Hr Hlast) as [q [Hq Eq]].
      rewrite Eq in HK. exact (Hext LastEnd Hrn q Hq HK).
  - assert (Hrel : reconnect_list (scale_classifier h k)
      (nonadjacent_sides l r) (nonadjacent_sides l' r')).
    { unfold nonadjacent_sides. apply Forall2_app.
      - apply reconnect_removelast. exact (reconnect_left _ _ _ _ _ _ Hr).
      - apply reconnect_tl. exact (reconnect_right _ _ _ _ _ _ Hr). }
    intros s' p Hin Hp.
    destruct (reconnect_in_old _ _ _ _ Hrel Hin) as [s [Hs Hrec]].
    exact (reconnected_triangle_avoids_sub _ _ _ _ p Hrec (Htri s Hs) Hp).
Qed.

(* 共通倍率はこの存在証明の内部で選び、最終的な端点変位に吸収する。 *)
Theorem embed_sparsely_prepared_from_spec :
  forall ds1 sub_ds ds2 l sub r k,
  PreparedSparseEmbedding ds1 sub_ds ds2 l sub r ->
  ClassificationSpec l sub r k ->
  exists l' r',
    PreparedSparseEmbedding ds1 sub_ds ds2 l' sub r' /\
    ~ close (l'++sub++r') /\ sparse_around l' sub r'.
Proof.
  intros ds1 sub_ds ds2 l sub r k Hprep Hspec.
  pose proof (prepared_geometry _ _ _ _ _ _ Hprep) as Hgeom.
  pose proof (prepared_whole_sparse _ _ _ _ _ _ Hprep) as Hsparse.
  pose proof (prepared_whole_embed _ _ _ _ _ _ Hprep) as Hembed.
  pose proof (prepared_extensions_disjoint _ _ _ _ _ _ Hprep) as Hext.
  destruct (classified_all_triangles_eventually_escape _ _ _ _ Hspec)
    as [a [Ha Htri]].
  destruct (classified_extensions_eventually_escape _ _ _ _ Hgeom Hspec Hsparse
    (ex_intro _ (ds1++sub_ds++ds2) Hembed)) as [b [Hb Hex]].
  destruct (reconnect_split_exists _ _ _ _ Hspec) as [c [Hc Hrec]].
  set (h := Rmax c (Rmax a b)).
  assert (Hha : a<=h) by (unfold h; pose proof (Rmax_r c (Rmax a b)); pose proof (Rmax_l a b); lra).
  assert (Hhb : b<=h) by (unfold h; pose proof (Rmax_r c (Rmax a b)); pose proof (Rmax_r a b); lra).
  assert (Hhc : c<=h) by (unfold h; apply Rmax_l).
  assert (Hh : 0<=h) by lra.
  destruct (Hrec h Hhc) as [l' [r' Hr]].
  pose proof (reconnect_whole_list _ _ _ _ _ _ (scale_sub_fixed _ _ _ _ h Hspec) Hr) as Hrel.
  pose proof (reconnect_list_embed _ _ _ _ Hrel Hembed) as Hnew.
  pose proof (reconnect_preserves_sparse (ds1++sub_ds++ds2) l sub r k h l' r' Hgeom Hspec Hsparse Hembed
    Hh Hr (Htri h Hha)) as Hsparse'.
  pose proof (reconnect_preserves_extensions_disjoint _ _ _ _ _ _ _ Hgeom Hspec Hext
    Hh Hr) as Hext'.
  assert (Hprep' : PreparedSparseEmbedding ds1 sub_ds ds2 l' sub r').
  { constructor.
    - exact (reconnect_list_embed _ _ _ _ (reconnect_left _ _ _ _ _ _ Hr)
        (prepared_left_embed _ _ _ _ _ _ Hprep)).
    - exact (prepared_sub_embed _ _ _ _ _ _ Hprep).
    - exact (reconnect_list_embed _ _ _ _ (reconnect_right _ _ _ _ _ _ Hr)
        (prepared_right_embed _ _ _ _ _ _ Hprep)).
    - exact Hnew.
    - exact Hsparse'.
    - exact Hext'.
    - exact (prepared_geometry_transport _ _ _ _ _ Hgeom).
    - exact (prepared_single_replacement _ _ _ _ _ _ Hprep).
    - exact (prepared_pair_replacement _ _ _ _ _ _ Hprep). }
  exists l',r'. split; [exact Hprep' |]. split.
  - apply (sparse_extensions_open (ds1++sub_ds++ds2)).
    + intro E. apply app_eq_nil in E as [_ E].
      apply app_eq_nil in E as [E _].
      exact (prepared_sub_nonempty _ _ _ Hgeom E).
    + exact Hnew.
    + exact Hsparse'.
    + exact Hext'.
  - exact (reconnect_gives_sparse_around _ _ _ _ _ _ _ Hgeom Hspec Hr (Htri h Hha) (Hex h Hhb)).
Qed.

(* 全域の疎性と二延長線の非交差を保ち、sub の閉長方形から外側を退避させる。
   sub の端点と傾きによる局所置換条件も満たす開埋め込みを得る。 *)
Theorem embed_sparsely_prepared : forall ds1 sub_ds ds2,
  AdmissibleDirs (ds1++sub_ds++ds2) ->
  (exists l sub r, PreparedSparseEmbedding ds1 sub_ds ds2 l sub r) ->
  exists l sub r, PreparedSparseEmbedding ds1 sub_ds ds2 l sub r /\
    ~ close (l++sub++r) /\ sparse_around l sub r.
Proof.
  intros ds1 sub_ds ds2 Hadm Hprep.
  destruct (prepared_classification_exists _ _ _ Hadm Hprep)
    as [l [sub [r [k [Hp Hspec]]]]].
  destruct (embed_sparsely_prepared_from_spec _ _ _ _ _ _ _ Hp Hspec)
    as [l' [r' Hout]].
  exists l',sub,r'. exact Hout.
Qed.
