Require Export Sparse.Reconnect.
From Stdlib Require Import Lra Lia Psatz Field.
Import ListNotations.

Lemma reconnect_segment_from_endpoints : forall k old new,
  endpoint_displacements_ordered k old ->
  init new = move_point k (init old) ->
  term new = move_point k (term old) ->
  orn_seg new = orn_seg old ->
  reconnect_segment k old new.
Proof.
  intros k old new Horder Hi Ht Ho. constructor; try assumption.
  apply same_primitive_of_axis_orders; try assumption;
    rewrite Hi, Ht; apply (moved_endpoint_axis_orders k old Horder).
Qed.

Lemma reconnect_one_spec : forall k seg H,
  reconnect_segment k seg (reconnect_one k seg H).
Proof.
  intros. apply reconnect_segment_from_endpoints; [exact H | | |];
    unfold reconnect_one; [apply make_seg_init | apply make_seg_term | apply make_seg_orn].
Qed.

Lemma reconnect_list_length : forall k xs ys,
  reconnect_list k xs ys -> length xs = length ys.
Proof. intros k xs ys H. induction H; simpl; congruence. Qed.

Lemma reconnect_nth_old : forall k xs ys i y,
  reconnect_list k xs ys -> nth_error ys i = Some y ->
  exists x, nth_error xs i = Some x /\ reconnect_segment k x y.
Proof.
  intros k xs ys i y H. revert i y.
  induction H; intros [|i] z Hz; simpl in Hz; try discriminate.
  - inversion Hz; subst. exists x. auto.
  - destruct (IHForall2 i z Hz) as [old [Ho Hr]].
    exists old. split; [exact Ho | exact Hr].
Qed.

Lemma reconnect_nth_new : forall k xs ys i x,
  reconnect_list k xs ys -> nth_error xs i = Some x ->
  exists y, nth_error ys i = Some y /\ reconnect_segment k x y.
Proof.
  intros k xs ys i x H. revert i x.
  induction H; intros [|i] z Hz; simpl in Hz; try discriminate.
  - inversion Hz; subst. exists y. auto.
  - destruct (IHForall2 i z Hz) as [new [Hn Hr]].
    exists new. split; [exact Hn | exact Hr].
Qed.

Lemma reconnect_list_exists : forall k xs,
  (forall seg, In seg xs -> endpoint_displacements_ordered k seg) ->
  exists ys, reconnect_list k xs ys.
Proof.
  intros k xs. induction xs as [|seg tail IH]; intros H.
  - exists []; constructor.
  - destruct (IH ltac:(intros; apply H; now right)) as [ys Hys].
    exists (reconnect_one k seg (H seg ltac:(now left)) :: ys).
    constructor; [apply reconnect_one_spec | exact Hys].
Qed.

Lemma reconnect_list_connected : forall k xs ys,
  reconnect_list k xs ys -> connected xs -> connected ys.
Proof.
  intros k xs ys Hr Hconn i a b Ha Hb.
  destruct (reconnect_nth_old k xs ys i a Hr Ha) as [oa [Hoa Hra]].
  destruct (reconnect_nth_old k xs ys (S i) b Hr Hb) as [ob [Hob Hrb]].
  rewrite (reconnect_term _ _ _ Hra), (reconnect_init _ _ _ Hrb).
  now rewrite (Hconn i oa ob Hoa Hob).
Qed.

(* 連結性と各 primitive の保存から、同じ方向列の埋め込みを得る。 *)
Lemma reconnect_list_embed : forall k ds xs ys,
  reconnect_list k xs ys -> embed_listDir ds xs -> embed_listDir ds ys.
Proof.
  intros k ds xs ys Hr He.
  apply (embed_scurve_transfer_same_primitive ds xs ys He).
  - symmetry. now apply (reconnect_list_length k).
  - intros i s t Hs Ht.
    destruct (reconnect_nth_old k xs ys i t Hr Ht) as [old [Ho Hrec]].
    rewrite Hs in Ho. inversion Ho; subst. exact (reconnect_primitive _ _ _ Hrec).
  - apply (reconnect_list_connected k xs ys Hr).
    exact (embed_listDir_connected ds xs He).
Qed.

Lemma reconnect_list_reflexive : forall k xs,
  (forall p, onSegmentlist xs p -> k p = 0) ->
  reconnect_list k xs xs.
Proof.
  intros k xs. induction xs as [|seg tail IH]; intros H.
  - constructor.
  - constructor.
    + constructor.
      * symmetry. apply move_point_zero. apply H. exists seg; split; [now left | apply onInit].
      * symmetry. apply move_point_zero. apply H. exists seg; split; [now left | apply onTerm].
      * reflexivity.
    + apply IH. intros p [s [Hs Hp]]. apply H. exists s. split; [now right | exact Hp].
Qed.

Lemma reconnect_whole_list : forall k l sub r l' r',
  (forall p, onSegmentlist sub p -> k p = 0) ->
  reconnect_split k l sub r l' r' ->
  reconnect_list k (l ++ sub ++ r) (l' ++ sub ++ r').
Proof.
  intros k l sub r l' r' Hfix Hr.
  apply Forall2_app; [exact (reconnect_left _ _ _ _ _ _ Hr) |].
  apply Forall2_app; [now apply reconnect_list_reflexive | exact (reconnect_right _ _ _ _ _ _ Hr)].
Qed.

Lemma reconnect_list_head : forall k xs ys,
  xs <> [] -> reconnect_list k xs ys ->
  reconnect_segment k (hd_segment xs) (hd_segment ys).
Proof. intros k xs ys Hne Hr. destruct Hr; [contradiction | exact H]. Qed.

Lemma reconnect_list_last : forall k xs ys,
  xs <> [] -> reconnect_list k xs ys ->
  reconnect_segment k (last_segment xs) (last_segment ys).
Proof.
  intros k xs ys Hne Hr.
  pose proof (reconnect_list_length k xs ys Hr) as Hlen.
  assert (Hyn : ys <> []) by (intro E; subst ys; destruct xs; simpl in Hlen; congruence).
  pose proof (@nth_error_last Segment ys default_segment Hyn) as Hlast.
  destruct (reconnect_nth_old k xs ys (length ys - 1) (last_segment ys) Hr Hlast)
    as [s [Hs Hrec]].
  rewrite <- Hlen in Hs.
  pose proof (@nth_error_last Segment xs default_segment Hne) as Hold.
  rewrite Hold in Hs. inversion Hs; subst. exact Hrec.
Qed.

(* 再接続後の上下境界は、元の境界に補間した変位を加えたもの。 *)
Lemma reconnect_boundary_values : forall k old new x,
  reconnect_segment k old new ->
  triangle_lower new x = triangle_lower old x + lower_displacement k old x /\
  triangle_upper new x = triangle_upper old x + upper_displacement k old x.
Proof.
  intros k old new x [Hi Ht Hp].
  unfold triangle_lower, triangle_upper, lower_displacement, upper_displacement,
    lower_value, upper_value.
  rewrite Hp.
  unfold chord_value, low_value, high_value, segment_x_parameter, init_x, term_x.
  rewrite Hp, Hi, Ht.
  unfold move_point. simpl.
  destruct (C_of (primitive_segment old)), (V_of (primitive_segment old)); simpl; split; ring.
Qed.

Lemma reconnect_x_range : forall k old new x,
  reconnect_segment k old new ->
  (segment_x_range new x <-> segment_x_range old x).
Proof.
  intros k old new x [Hi Ht Hp].
  unfold segment_x_range, init_x, term_x. rewrite Hi, Ht. reflexivity.
Qed.


Lemma reconnect_left_exists : forall k xs,
  (forall seg, In seg xs -> endpoint_displacements_ordered k seg) ->
  (xs <> [] -> reconnect_init_slope
    (move_point k (init (hd_segment xs))) (move_point k (term (hd_segment xs)))
    (orn_seg (hd_segment xs)) (slope_init (hd_segment xs))) ->
  exists ys, reconnect_list k xs ys /\
    (xs <> [] -> slope_init (hd_segment ys) = slope_init (hd_segment xs)).
Proof.
  intros k [|seg tail] Ho Hs.
  - exists []; split; [constructor | contradiction].
  - destruct (reconnect_list_exists k tail ltac:(intros; apply Ho; now right))
      as [ys Hys].
    pose (Hs' := Hs ltac:(discriminate)).
    set (s' := make_seg_init_slope
      (move_point k (init seg)) (move_point k (term seg)) (orn_seg seg) (slope_init seg) Hs').
    pose proof (make_seg_init_slope_spec
      (move_point k (init seg)) (move_point k (term seg)) (orn_seg seg) (slope_init seg) Hs')
      as [Hi [Ht [Horn Hslope]]].
    exists (s' :: ys). split.
    + constructor; [|exact Hys].
      apply reconnect_segment_from_endpoints; auto. apply Ho. now left.
    + intros _. exact Hslope.
Qed.

Lemma reconnect_right_exists : forall k xs,
  (forall seg, In seg xs -> endpoint_displacements_ordered k seg) ->
  (xs <> [] -> reconnect_term_slope
    (move_point k (init (last_segment xs))) (move_point k (term (last_segment xs)))
    (orn_seg (last_segment xs)) (slope_term (last_segment xs))) ->
  exists ys, reconnect_list k xs ys /\
    (xs <> [] -> slope_term (last_segment ys) = slope_term (last_segment xs)).
Proof.
  intros k xs. induction xs as [|seg tail IH]; intros Ho Hs.
  - exists []; split; [constructor | contradiction].
  - destruct tail as [|next tail].
    + pose (Hs' := Hs ltac:(discriminate)).
      set (s' := make_seg_term_slope
        (move_point k (init seg)) (move_point k (term seg)) (orn_seg seg) (slope_term seg) Hs').
      pose proof (make_seg_term_slope_spec
        (move_point k (init seg)) (move_point k (term seg)) (orn_seg seg) (slope_term seg) Hs')
        as [Hi [Ht [Horn Hslope]]].
      exists [s']. split.
      * constructor; [|constructor].
        apply reconnect_segment_from_endpoints; auto. apply Ho. now left.
      * intros _. exact Hslope.
    + destruct (IH ltac:(intros; apply Ho; now right)
                   ltac:(intros _; apply Hs; discriminate)) as [ys [Hys Hlast]].
      pose (s' := reconnect_one k seg (Ho seg ltac:(now left))).
      exists (s' :: ys). split.
      * constructor; [apply reconnect_one_spec | exact Hys].
      * intros _.
        assert (Hne : ys <> []).
        { intro E. subst ys. inversion Hys. }
        change (slope_term (last_segment ([s'] ++ ys)) =
                slope_term (last_segment (next :: tail))).
        rewrite last_app_nonnil by exact Hne.
        apply Hlast. discriminate.
Qed.

(* 有限列の存在だけを示し、存在命題から大域的な選択関数は作らない。 *)
Lemma reconnect_split_exists : forall l sub r k,
  ClassificationSpec l sub r k ->
  exists h0, 0 <= h0 /\ forall h, h0 <= h ->
    exists l' r', reconnect_split (scale_classifier h k) l sub r l' r'.
Proof.
  intros l sub r k Hspec.
  destruct (classified_end_slopes _ _ _ _ Hspec) as [h0 [H0 Hs]].
  exists h0. split; [exact H0 |]. intros h Hh.
  destruct (Hs h Hh) as [Hleft Hright].
  assert (Hord : forall seg, In seg (l ++ sub ++ r) ->
    endpoint_displacements_ordered (scale_classifier h k) seg).
  { intros seg Hin. apply ordered_scale_classifier; [lra |].
    exact (classified_segment_endpoints_monotone _ _ _ _ Hspec seg Hin). }
  destruct (reconnect_left_exists (scale_classifier h k) l
    ltac:(intros; apply Hord; apply in_or_app; now left) Hleft)
    as [l' [Hl Hlslope]].
  destruct (reconnect_right_exists (scale_classifier h k) r
    ltac:(intros; apply Hord; apply in_or_app; right; apply in_or_app; now right) Hright)
    as [r' [Hr Hrslope]].
  exists l', r'. constructor; assumption.
Qed.

Lemma scale_sub_fixed : forall l sub r k h,
  ClassificationSpec l sub r k ->
  forall p, onSegmentlist sub p -> scale_classifier h k p = 0.
Proof.
  intros l sub r k h Hspec p Hp. unfold scale_classifier.
  rewrite (classified_sub_fixed _ _ _ _ Hspec p Hp). ring.
Qed.

Lemma reconnect_head_data : forall k l sub r l' r',
  sub <> [] ->
  (forall p, onSegmentlist sub p -> k p = 0) ->
  reconnect_split k l sub r l' r' ->
  init (hd_segment (l' ++ sub ++ r')) =
    move_point k (init (hd_segment (l ++ sub ++ r))) /\
  slope_init (hd_segment (l' ++ sub ++ r')) =
    slope_init (hd_segment (l ++ sub ++ r)).
Proof.
  intros k l sub r l' r' Hne Hfix Hr.
  destruct (reconnect_left _ _ _ _ _ _ Hr) as [|a a' tail tail' Ha Htail].
  - destruct sub as [|b bs]; [contradiction |]. simpl.
    split; [symmetry; apply move_point_zero; apply Hfix;
      exists b; split; [now left | apply onInit] | reflexivity].
  - split; [exact (reconnect_init _ _ _ Ha) |].
    apply (reconnect_head_slope _ _ _ _ _ _ Hr). discriminate.
Qed.

Lemma reconnect_last_data : forall k l sub r l' r',
  sub <> [] ->
  (forall p, onSegmentlist sub p -> k p = 0) ->
  reconnect_split k l sub r l' r' ->
  term (last_segment (l' ++ sub ++ r')) =
    move_point k (term (last_segment (l ++ sub ++ r))) /\
  slope_term (last_segment (l' ++ sub ++ r')) =
    slope_term (last_segment (l ++ sub ++ r)).
Proof.
  intros k l sub r l' r' Hne Hfix Hr.
  pose proof (reconnect_right _ _ _ _ _ _ Hr) as Hrr.
  destruct r as [|a tail].
  - inversion Hrr; subst r'. rewrite !app_nil_r.
    rewrite !last_app_nonnil by exact Hne.
    split; [symmetry; apply move_point_zero; apply Hfix;
      apply onSegmentlist_term_last; exact Hne | reflexivity].
  - assert (Hrp : r' <> []) by (intro E; rewrite E in Hrr; inversion Hrr).
    rewrite !app_assoc.
    rewrite !last_app_nonnil by (try exact Hrp; discriminate).
    split.
    + exact (reconnect_term _ _ _
        (reconnect_list_last k (a::tail) r' ltac:(discriminate) Hrr)).
    + apply (reconnect_last_slope _ _ _ _ _ _ Hr). discriminate.
Qed.

Lemma move_point_as_translation : forall k p,
  move_point k p = translate_pt (0,k p) p.
Proof.
  intros k [x y]. unfold move_point, translate_pt; simpl.
  f_equal; ring.
Qed.

Lemma head_extension_preimage : forall k old new p,
  init new = move_point k (init old) ->
  slope_init new = slope_init old ->
  onHead new p ->
  exists q, onHead old q /\ p = translate_pt (0,k (init old)) q.
Proof.
  intros k old new p Hi Hs Hp.
  set (v := (0,k (init old))).
  assert (Ht : init new = init (translate_seg v old)).
  { rewrite translate_seg_init, Hi, move_point_as_translation. reflexivity. }
  assert (Hs' : slope_init new = slope_init (translate_seg v old)).
  { now rewrite translate_seg_slope_init. }
  apply (proj1 (head_extension_determined_by_init_slope
    new (translate_seg v old) Ht Hs' p)) in Hp.
  destruct Hp as [t [Ht0 Hpoint]]. rewrite translate_seg_point in Hpoint.
  exists (point old t). split; [exists t; auto | symmetry; exact Hpoint].
Qed.

Lemma last_extension_preimage : forall k old new p,
  term new = move_point k (term old) ->
  slope_term new = slope_term old ->
  onLast new p ->
  exists q, onLast old q /\ p = translate_pt (0,k (term old)) q.
Proof.
  intros k old new p Hi Hs Hp.
  set (v := (0,k (term old))).
  assert (Ht : term new = term (translate_seg v old)).
  { rewrite translate_seg_term, Hi, move_point_as_translation. reflexivity. }
  assert (Hs' : slope_term new = slope_term (translate_seg v old)).
  { now rewrite translate_seg_slope_term. }
  apply (proj1 (last_extension_determined_by_term_slope
    new (translate_seg v old) Ht Hs' p)) in Hp.
  destruct Hp as [t [Ht0 Hpoint]]. rewrite translate_seg_point in Hpoint.
  exists (point old t). split; [exists t; auto | symmetry; exact Hpoint].
Qed.

Lemma strict_head_extension_preimage : forall k old new p,
  init new = move_point k (init old) ->
  slope_init new = slope_init old ->
  (exists t, t < 0 /\ point new t = p) ->
  exists q, (exists t, t < 0 /\ point old t = q) /\
    p = translate_pt (0,k (init old)) q.
Proof.
  intros k old new p Hi Hs [u [Hu Hup]].
  assert (Hpn : p <> init new).
  { intro E. unfold init in E. rewrite <- Hup in E.
    apply point_injective in E. lra. }
  destruct (head_extension_preimage k old new p Hi Hs
    ltac:(exists u; split; [lra | exact Hup])) as [q [[t [Ht Htq]] Hp]].
  assert (Htn : t <> 0).
  { intro E. subst t. change (init old = q) in Htq.
    subst q. apply Hpn. rewrite Hp, Hi, move_point_as_translation. reflexivity. }
  exists q. split; [exists t; split; [lra | exact Htq] | exact Hp].
Qed.

Definition triangle_escapes_sub (d : EndpointClassifier) (sub : list Segment) (seg : Segment) : Prop :=
  (forall x, sub_x_left sub seg <= x <= sub_x_right sub seg ->
    ry1 (rect_of sub) < triangle_lower seg x + lower_displacement d seg x) \/
  (forall x, sub_x_left sub seg <= x <= sub_x_right sub seg ->
    triangle_upper seg x + upper_displacement d seg x < ry0 (rect_of sub)).

Lemma eventually_above : forall a d c,
  0 <= d -> (d = 0 -> c < a) ->
  exists h0, 0 <= h0 /\ forall h, h0 <= h -> c < a+h*d.
Proof.
  intros a d c Hd Hz. destruct (Rlt_dec 0 d) as [Hp | Hnp].
  - exists (Rmax 0 ((c-a)/d+1)). split; [apply Rmax_l |].
    intros h Hh. pose proof (Rmax_r 0 ((c-a)/d+1)).
    assert (He : ((c-a)/d)*d = c-a) by (field; lra).
    nra.
  - assert (He : d=0) by lra. exists 0. split; [lra |].
    intros h Hh. specialize (Hz He). rewrite He. lra.
Qed.

Lemma finite_eventual_bound : forall (A : Type) (xs : list A) (P : A -> R -> Prop),
  (forall x, In x xs -> exists h0, 0 <= h0 /\ forall h, h0 <= h -> P x h) ->
  exists h0, 0 <= h0 /\ forall h, h0 <= h -> forall x, In x xs -> P x h.
Proof.
  intros A xs P. induction xs as [|x tail IH]; intros H.
  - exists 0. split; [lra | intros h Hh x Hx; contradiction].
  - destruct (H x ltac:(now left)) as [a [Ha Hax]].
    destruct (IH ltac:(intros; apply H; now right)) as [b [Hb Hbt]].
    exists (Rmax a b). split; [pose proof (Rmax_l a b); lra |].
    intros h Hh y [Hy | Hy].
    + subst y. apply Hax. pose proof (Rmax_l a b); lra.
    + apply Hbt; [pose proof (Rmax_r a b); lra | exact Hy].
Qed.

(* S5 の有限個の端点条件から、各三角形を退避させる共通倍率を得る。 *)
Lemma classified_triangle_eventually_escapes : forall l sub r k seg,
  ClassificationSpec l sub r k -> In seg (nonadjacent_sides l r) ->
  exists h0, 0 <= h0 /\ forall h, h0 <= h ->
    triangle_escapes_sub (scale_classifier h k) sub seg.
Proof.
  intros l sub r k seg Hspec Hin.
  set (lo := sub_x_left sub seg). set (hi := sub_x_right sub seg).
  destruct (Rle_dec lo hi) as [Hrange | Hempty].
  2: { exists 0. split; [lra |]. intros h Hh. left. intros x Hx.
       fold lo hi in Hx. exfalso; lra. }
  assert (Hlo : sub_overlap_endpoint sub seg lo) by (split; [exact Hrange | now left]).
  assert (Hhi : sub_overlap_endpoint sub seg hi) by (split; [exact Hrange | now right]).
  destruct (classified_segment_escape _ _ _ _ Hspec seg Hin) as [Hup | Hdown].
  - destruct (Hup lo Hlo) as [Dlo Zlo]. destruct (Hup hi Hhi) as [Dhi Zhi].
    destruct (eventually_above _ _ _ Dlo Zlo) as [a [Ha Hla]].
    destruct (eventually_above _ _ _ Dhi Zhi) as [b [Hb Hhb]].
    exists (Rmax a b). split; [pose proof (Rmax_l a b); lra |].
    intros h Hh. left. intros x Hx.
    rewrite lower_value_scale.
    apply (affine_above_on_interval
      (fun z => triangle_lower seg z + h*lower_displacement k seg z) lo hi _ x).
    + apply affine_add; [apply lower_value_affine |].
      apply affine_scale. apply lower_value_affine.
    + exact Hx.
    + apply Hla. pose proof (Rmax_l a b); lra.
    + apply Hhb. pose proof (Rmax_r a b); lra.
  - destruct (Hdown lo Hlo) as [Dlo Zlo]. destruct (Hdown hi Hhi) as [Dhi Zhi].
    assert (Elo : exists a, 0 <= a /\ forall h, a <= h ->
      triangle_upper seg lo+h*upper_displacement k seg lo < ry0 (rect_of sub)).
    { destruct (eventually_above (-triangle_upper seg lo) (-upper_displacement k seg lo)
        (-ry0 (rect_of sub)) ltac:(lra) ltac:(intros H; assert (E : upper_displacement k seg lo=0) by lra; specialize (Zlo E); lra))
        as [a [Ha Hla]]. exists a. split; [exact Ha |]. intros; specialize (Hla h H); nra. }
    assert (Ehi : exists b, 0 <= b /\ forall h, b <= h ->
      triangle_upper seg hi+h*upper_displacement k seg hi < ry0 (rect_of sub)).
    { destruct (eventually_above (-triangle_upper seg hi) (-upper_displacement k seg hi)
        (-ry0 (rect_of sub)) ltac:(lra) ltac:(intros H; assert (E : upper_displacement k seg hi=0) by lra; specialize (Zhi E); lra))
        as [b [Hb Hhb]]. exists b. split; [exact Hb |]. intros; specialize (Hhb h H); nra. }
    destruct Elo as [a [Ha Hla]]. destruct Ehi as [b [Hb Hhb]].
    exists (Rmax a b). split; [pose proof (Rmax_l a b); lra |].
    intros h Hh. right. intros x Hx.
    rewrite upper_value_scale.
    apply (affine_below_on_interval
      (fun z => triangle_upper seg z+h*upper_displacement k seg z) lo hi _ x).
    + apply affine_add; [apply upper_value_affine |].
      apply affine_scale. apply upper_value_affine.
    + exact Hx.
    + apply Hla. pose proof (Rmax_l a b); lra.
    + apply Hhb. pose proof (Rmax_r a b); lra.
Qed.

Lemma classified_all_triangles_eventually_escape : forall l sub r k,
  ClassificationSpec l sub r k ->
  exists h0, 0 <= h0 /\ forall h, h0 <= h ->
    forall seg, In seg (nonadjacent_sides l r) ->
      triangle_escapes_sub (scale_classifier h k) sub seg.
Proof.
  intros. apply finite_eventual_bound. intros.
  eapply classified_triangle_eventually_escapes; eassumption.
Qed.

Lemma reconnected_triangle_avoids_sub : forall d sub old new p,
  reconnect_segment d old new -> triangle_escapes_sub d sub old ->
  in_segment_triangle new p -> ~ in_rect_or_endpoints_at sub p.
Proof.
  intros d sub old new [x y] Hrec Hclear Hp Hrect.
  apply in_triangle_iff_fibre in Hp. destruct Hp as [Hx Hy].
  apply (proj1 (reconnect_x_range d old new x Hrec)) in Hx.
  unfold in_rect_or_endpoints_at, in_closed_rect in Hrect.
  destruct Hrect as [Hsx Hsy].
  assert (Hcommon : sub_x_left sub old <= x <= sub_x_right sub old).
  { apply common_x_bounds. split; [exact Hx | exact Hsx]. }
  destruct (reconnect_boundary_values d old new x Hrec) as [Hlow Hup].
  rewrite Hlow,Hup in Hy.
  destruct Hclear as [H | H]; specialize (H x Hcommon); simpl in *; lra.
Qed.


Lemma strict_last_extension_preimage : forall k old new p,
  term new = move_point k (term old) ->
  slope_term new = slope_term old ->
  (exists t, 1 < t /\ point new t = p) ->
  exists q, (exists t, 1 < t /\ point old t = q) /\
    p = translate_pt (0,k (term old)) q.
Proof.
  intros k old new p Hi Hs [u [Hu Hup]].
  assert (Hpn : p <> term new).
  { intro E. unfold term in E. rewrite <- Hup in E.
    apply point_injective in E. lra. }
  destruct (last_extension_preimage k old new p Hi Hs
    ltac:(exists u; split; [lra | exact Hup])) as [q [[t [Ht Htq]] Hp]].
  assert (Htn : t <> 1).
  { intro E. subst t. change (term old = q) in Htq.
    subst q. apply Hpn. rewrite Hp, Hi, move_point_as_translation. reflexivity. }
  exists q. split; [exists t; split; [lra | exact Htq] | exact Hp].
Qed.

Lemma reconnect_whole_extension_preimage : forall d l sub r l' r' which p,
  sub <> [] -> (forall q, onSegmentlist sub q -> d q=0) ->
  reconnect_split d l sub r l' r' ->
  on_end_extension which (l' ++ sub ++ r') p ->
  exists q, on_end_extension which (l ++ sub ++ r) q /\
    p=translate_pt (0,d (extension_anchor which (l ++ sub ++ r))) q.
Proof.
  intros d l sub r l' r' which p Hne Hfix Hr Hp.
  destruct which.
  - destruct (reconnect_head_data _ _ _ _ _ _ Hne Hfix Hr) as [Hi Hs].
    eapply head_extension_preimage; eassumption.
  - destruct (reconnect_last_data _ _ _ _ _ _ Hne Hfix Hr) as [Hi Hs].
    eapply last_extension_preimage; eassumption.
Qed.

Lemma reconnect_whole_strict_extension_preimage : forall d l sub r l' r' which p,
  sub <> [] -> (forall q, onSegmentlist sub q -> d q=0) ->
  reconnect_split d l sub r l' r' ->
  on_strict_extension which (l' ++ sub ++ r') p ->
  exists q, on_strict_extension which (l ++ sub ++ r) q /\
    p=translate_pt (0,d (extension_anchor which (l ++ sub ++ r))) q.
Proof.
  intros d l sub r l' r' which p Hne Hfix Hr Hp.
  destruct which.
  - destruct (reconnect_head_data _ _ _ _ _ _ Hne Hfix Hr) as [Hi Hs].
    eapply strict_head_extension_preimage; eassumption.
  - destruct (reconnect_last_data _ _ _ _ _ _ Hne Hfix Hr) as [Hi Hs].
    eapply strict_last_extension_preimage; eassumption.
Qed.
