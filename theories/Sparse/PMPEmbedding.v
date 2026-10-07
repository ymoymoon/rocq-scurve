Require Export Sparse.ReconnectWholeProof.
Require Import Stdlib.Logic.ClassicalDescription.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Relations.Relation_Operators Relations.Operators_Properties.

(* Plus 側の目的三角形に接触する外側だけを Up の出発点にする。 *)
Inductive pmp_up_seed (l sub r : list Segment) : Point -> Prop :=
| pmp_body_seed : forall seg p endpoint,
    In seg (nonadjacent_sides l r) ->
    in_segment_triangle seg p -> in_sub_triangle Plus sub p ->
    endpoint_of_seg seg endpoint -> pmp_up_seed l sub r endpoint
| pmp_head_seed : forall p,
    l <> [] -> onHead_extend_strict (l ++ sub ++ r) p ->
    in_sub_triangle Plus sub p ->
    pmp_up_seed l sub r (init (hd_segment (l ++ sub ++ r)))
| pmp_last_seed : forall p,
    r <> [] -> onLast_extend_strict (l ++ sub ++ r) p ->
    in_sub_triangle Plus sub p ->
    pmp_up_seed l sub r (term (last_segment (l ++ sub ++ r))).

(* 共通順序に、sub の x 範囲を通る外側の両端を同時に動かす制約を加える。 *)
Inductive pmp_order_step (l sub r : list Segment) : Point -> Point -> Prop :=
| pmp_common_step : forall p q,
    endpoint_order_step l sub r p q -> pmp_order_step l sub r p q
| pmp_uniform_step : forall seg p a b,
    In seg (nonadjacent_sides l r) -> onSegment seg p ->
    in_sub_x_range sub p -> endpoint_of_seg seg a -> endpoint_of_seg seg b ->
    pmp_order_step l sub r a b.

Definition pmp_order l sub r := clos_refl_trans Point (pmp_order_step l sub r).
Definition pmp_up_reachable l sub r p : Prop :=
  exists seed, pmp_up_seed l sub r seed /\ pmp_order l sub r seed p.

Definition classify_pmp (l sub r : list Segment) (p : Point) : Region :=
  if excluded_middle_informative (onSegmentlist sub p) then RegFix
  else if excluded_middle_informative (pmp_up_reachable l sub r p) then RegUp
  else RegFix.

(* Up の順序閉包が固定部分 sub に到達しないこと。分類構成の正当性として示す。 *)
Definition pmp_sources_safe l sub r : Prop :=
  forall p, pmp_up_reachable l sub r p -> ~ onSegmentlist sub p.

Lemma classify_pmp_only_up_or_fix : forall l sub r p,
  classify_pmp l sub r p = RegUp \/ classify_pmp l sub r p = RegFix.
Proof.
  intros. unfold classify_pmp.
  destruct excluded_middle_informative; [now right |].
  destruct excluded_middle_informative; [now left | now right].
Qed.

Lemma classify_pmp_sub_fixed : forall l sub r p,
  onSegmentlist sub p -> classify_pmp l sub r p = RegFix.
Proof.
  intros l sub r p Hp. unfold classify_pmp.
  destruct excluded_middle_informative; [reflexivity | contradiction].
Qed.

Lemma classify_pmp_up_iff : forall l sub r p,
  pmp_sources_safe l sub r ->
  (classify_pmp l sub r p = RegUp <-> pmp_up_reachable l sub r p).
Proof.
  intros l sub r p Hsafe. unfold classify_pmp.
  destruct (excluded_middle_informative (onSegmentlist sub p)) as [Hon | Hon].
  - split; [discriminate | intros Hup; exfalso; exact (Hsafe p Hup Hon)].
  - destruct (excluded_middle_informative (pmp_up_reachable l sub r p));
      split; intros; try reflexivity; try assumption; congruence.
Qed.

Lemma pmp_reachable_order : forall l sub r p q,
  pmp_up_reachable l sub r p -> pmp_order l sub r p q ->
  pmp_up_reachable l sub r q.
Proof.
  intros l sub r p q [seed [Hseed Hpath]] Hpq.
  exists seed. split; [exact Hseed | eapply rt_trans; eauto].
Qed.

Lemma pmp_common_order : forall l sub r p q,
  endpoint_order l sub r p q -> pmp_order l sub r p q.
Proof.
  intros l sub r p q H. induction H.
  - apply rt_step. now apply pmp_common_step.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

(* 到達可能性の閉包から領域順序を得る。幾何の難所は Hsafe に限定する。 *)
Lemma pmp_order_classified : forall l sub r p q,
  pmp_sources_safe l sub r -> pmp_order l sub r p q ->
  region_at_or_above (classify_pmp l sub r q) (classify_pmp l sub r p).
Proof.
  intros l sub r p q Hsafe Hpq.
  destruct (classify_pmp_only_up_or_fix l sub r p) as [Hp | Hp].
  - pose proof Hp as HpUp. apply (classify_pmp_up_iff l sub r p Hsafe) in Hp.
    pose proof (pmp_reachable_order l sub r p q Hp Hpq) as Hq.
    apply (classify_pmp_up_iff l sub r q Hsafe) in Hq.
    now left; rewrite HpUp, Hq.
  - destruct (classify_pmp_only_up_or_fix l sub r q) as [Hq | Hq].
    + rewrite Hp, Hq. now right; constructor.
    + now left; rewrite Hp, Hq.
Qed.

Lemma pmp_seed_classified_up : forall l sub r p,
  pmp_sources_safe l sub r -> pmp_up_seed l sub r p ->
  classify_pmp l sub r p = RegUp.
Proof.
  intros l sub r p Hsafe Hseed.
  apply (classify_pmp_up_iff l sub r p Hsafe).
  exists p. split; [exact Hseed | apply rt_refl].
Qed.

(* 共通順序と既存の四形ごとの傾き保存証明を、そのまま Up/Fix に使う。 *)
Lemma classify_pmp_spec : forall l sub r,
  pmp_sources_safe l sub r ->
  (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
  @PMPClassificationSpec l sub r (classify_pmp l sub r).
Proof.
  intros l sub r Hsafe Hembed.
  assert (Horder : forall p q,
    endpoint_order l sub r p q ->
    region_at_or_above (classify_pmp l sub r q) (classify_pmp l sub r p)).
  { intros p q Hp. eapply pmp_order_classified; [exact Hsafe |].
    now apply pmp_common_order. }
  constructor.
  - { constructor.
    - now apply classify_pmp_sub_fixed.
    - intros seg Hin. split; intros Hy; apply Horder;
        apply rt_step; apply order_core_step.
      + eapply order_on_segment with (seg := seg).
        * exact Hin.
        * now left.
        * now right.
        * lra.
      + eapply order_on_segment with (seg := seg).
        * exact Hin.
        * now right.
        * now left.
        * lra.
    - intros i j s t ps pt u v Hs Ht Hfar Hps Hpt Hu Hv Hx Hy.
      apply Horder. apply rt_step. apply order_core_step.
      apply (order_nonadjacent l sub r i j s t ps pt u v); assumption.
    - intros ph pl Hph Hpl Hx. split; intros Hy; apply Horder;
        apply rt_step; apply order_end_step.
      + eapply order_head_last; eauto; lra.
      + eapply order_last_head; eauto; lra.
    - intros seg e q Hin He Hq Hx. split; intros Hy; split; apply Horder;
        apply rt_step; apply order_end_step.
      + eapply order_head_below_segment; eauto; [lra | now left].
      + eapply order_head_below_segment; eauto; [lra | now right].
      + eapply order_segment_below_head; eauto; [lra | now left].
      + eapply order_segment_below_head; eauto; [lra | now right].
    - intros seg e q Hin He Hq Hx. split; intros Hy; split; apply Horder;
        apply rt_step; apply order_end_step.
      + eapply order_last_below_segment; eauto; [lra | now left].
      + eapply order_last_below_segment; eauto; [lra | now right].
      + eapply order_segment_below_last; eauto; [lra | now left].
      + eapply order_segment_below_last; eauto; [lra | now right].
    - eapply head_classification_preserves_init_slope_from_order; [|exact Hembed].
      intros. now apply Horder.
    - eapply last_classification_preserves_term_slope_from_order; [|exact Hembed].
      intros. now apply Horder. }
  - apply classify_pmp_only_up_or_fix.
  - intros seg p Hin Hon Hx. apply region_at_or_above_antisym;
      eapply pmp_order_classified; try exact Hsafe; apply rt_step;
      eapply pmp_uniform_step with (seg := seg) (p := p);
      eauto; unfold endpoint_of_seg; auto.
  - intros seg p Hin Htri Htarget. split; apply pmp_seed_classified_up;
      try exact Hsafe; eapply pmp_body_seed with (seg := seg) (p := p);
      eauto; unfold endpoint_of_seg; auto.
  - intros Hl p Hon Htri. apply pmp_seed_classified_up; [exact Hsafe |].
    eapply pmp_head_seed; eauto.
  - intros Hr p Hon Htri. apply pmp_seed_classified_up; [exact Hsafe |].
    eapply pmp_last_seed; eauto.
Qed.

(* PMP の幾何学的な証人。terminal 側の蓋だけを除き、分類に関する条件は含めない。 *)
Record PreparedPMPEmbedding (ds1 ds2 : list Direction)
    (l sub r : list Segment) : Prop := {
  pmp_left_embed : embed_listDir ds1 l;
  pmp_sub_embed : embed_listDir [Plus; Minus; Plus] sub;
  pmp_right_embed : embed_listDir ds2 r;
  pmp_whole_embed : embed_listDir (ds1 ++ [Plus; Minus; Plus] ++ ds2) (l ++ sub ++ r);
  pmp_whole_sparse : sparse_embedding (l ++ sub ++ r);
  pmp_extensions_disjoint : extensions_disjoint (l ++ sub ++ r);
  pmp_no_terminal_lid : ~ terminal_lid l sub r;
  pmp_replacement_slope : reconnect_slope
    (init (hd_segment sub)) (term (last_segment sub)) Plus
    (slope_init (hd_segment sub)) (slope_term (last_segment sub))
}.

(* PPMM の endpoint_order_up_path_not_reaches_sub に対応する PMP の source 分離。
   terminal 側の蓋を除いた幾何から、Up seed と sub 上の点を結ぶ順序パスを排除する。 *)
Lemma classify_pmp_sources_safe : forall l sub r,
  embed_listDir [Plus; Minus; Plus] sub ->
  sparse_embedding (l ++ sub ++ r) ->
  (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
  extensions_disjoint (l ++ sub ++ r) ->
  ~ terminal_lid l sub r ->
  forall upper lower,
    pmp_up_seed l sub r upper ->
    onSegmentlist sub lower ->
    ~ pmp_order l sub r upper lower.
Admitted.

Section TriangleClearance.
Variable classifier : list Segment -> list Segment -> list Segment -> EndpointClassifier.
Local Notation region_delta := ReconnectWholeByClassifier.region_delta.
Local Notation reconnect_one := (ReconnectByClassifier.reconnect_one classifier).
Local Notation reconnect_segs := (ReconnectByClassifier.reconnect_segs classifier).
Local Notation reconnect_whole := (ReconnectByClassifier.reconnect_whole classifier).
Local Notation reconnect_one_endpoints_orn := (ReconnectLocalByClassifier.reconnect_one_endpoints_orn classifier).
Local Notation operate_endpoints_reconnectable_from_spec := (ReconnectLocalByClassifier.operate_endpoints_reconnectable_from_spec classifier).

(* 両端を同じ量だけ動かした三角形は、旧三角形へ一律に引き戻せる。 *)
Lemma uniformly_reconnected_triangle_preimage : forall l sub r h s p g,
  @ReconnectClassificationSpec l sub r (classifier l sub r) ->
  h_large h sub -> In s (l ++ sub ++ r) ->
  classifier l sub r (init s) = g -> classifier l sub r (term s) = g ->
  in_segment_triangle (reconnect_one l sub r h s) p ->
  exists q, in_segment_triangle s q /\ p = shift h g q.
Proof.
  intros l sub r h s p g Hspec Hh Hin Hi Ht Hp.
  pose proof (operate_endpoints_reconnectable_from_spec l sub r h Hspec Hh s Hin) as Hrec.
  destruct (reconnect_one_endpoints_orn l sub r h s Hrec) as [Hinit [Hterm Horn]].
  destruct (ReconnectLocalByClassifier.operated_segment_axis_orders_from_spec
    classifier l sub r h s Hspec (proj1 Hh) Hin) as [Hx Hy].
  rewrite <- Hinit, <- Hterm in Hx, Hy.
  pose proof (same_primitive_of_axis_orders s (reconnect_one l sub r h s) Hx Hy Horn) as Hprimitive.
  assert (Hix : init_x (reconnect_one l sub r h s) = init_x s).
  { unfold init_x. rewrite Hinit. apply shift_fst. }
  assert (Htx : term_x (reconnect_one l sub r h s) = term_x s).
  { unfold term_x. rewrite Hterm. apply shift_fst. }
  assert (Hdi : init_y (reconnect_one l sub r h s) - init_y s = region_delta h g).
  { unfold init_y. rewrite Hinit. unfold ReconnectByClassifier.operate_point.
    rewrite Hi, shift_y_delta. lra. }
  assert (Hdt : term_y (reconnect_one l sub r h s) - term_y s = region_delta h g).
  { unfold term_y. rewrite Hterm. unfold ReconnectByClassifier.operate_point.
    rewrite Ht, shift_y_delta. lra. }
  assert (Hsign : 0 < (term_y s - init_y s) *
    (term_y (reconnect_one l sub r h s) - init_y (reconnect_one l sub r h s))).
  { pose proof (neq_init_term_y s). unfold init_y, term_y in *. nra. }
  destruct (triangle_vertical_shift_preimage s (reconnect_one l sub r h s) p
    Hix Htx ltac:(now rewrite Hprimitive) Hsign Hp) as [q [Hq [Hqx Hdy]]].
  rewrite Hdi, Hdt, Rmin_left, Rmax_left in Hdy by lra.
  exists q. split; [exact Hq |].
  apply injective_projections; [now rewrite shift_fst |].
  pose proof (shift_y_delta h g q). lra.
Qed.

(* x 範囲が重なる外側は一律 Up または Fix。Up は bbox より上へ出し、
   Fix なら入力三角形との接触規則に矛盾する。 *)
Lemma pmp_reconnect_one_avoids_triangle : forall l sub r h s p,
  sub <> [] -> @PMPClassificationSpec l sub r (classifier l sub r) ->
  h_large h sub -> height_clears_sub h l sub r ->
  In s (nonadjacent_sides l r) ->
  in_segment_triangle (reconnect_one l sub r h s) p ->
  ~ in_sub_triangle Plus sub p.
Proof.
  intros l sub r h s p Hne Hspec Hh Hclear Hin Hp Htarget.
  assert (Hwhole : In s (l ++ sub ++ r)) by now apply nonadjacent_sides_in_whole.
  pose proof (operate_endpoints_reconnectable_from_spec l sub r h Hspec Hh s Hwhole) as Hrec.
  destruct (reconnect_one_endpoints_orn l sub r h s Hrec) as [Hinit [Hterm _]].
  pose proof (in_segment_rect_or_endpoints_closed_bounds _ p (proj1 Hp)) as [Hpx Hpy].
  change (Rmin (fst (init (reconnect_one l sub r h s))) (fst (term (reconnect_one l sub r h s))) <= fst p <=
    Rmax (fst (init (reconnect_one l sub r h s))) (fst (term (reconnect_one l sub r h s)))) in Hpx.
  rewrite Hinit, Hterm in Hpx.
  unfold ReconnectByClassifier.operate_point in Hpx. rewrite !shift_fst in Hpx.
  destruct (segment_has_point_at_x s (fst p) Hpx) as [q [Hon Hqx]].
  assert (Hrange : in_sub_x_range sub q).
  { unfold in_sub_x_range. rewrite Hqx. exact (proj1 (proj1 Htarget)). }
  pose proof (pmp_segment_at_sub_x_uniform l sub r Hspec s q Hin Hon Hrange) as Hsame.
  destruct (pmp_only_up_or_fix l sub r Hspec (init s)) as [Hi | Hi].
  - assert (Ht : classifier l sub r (term s) = RegUp) by congruence.
    destruct (Hclear s Hwhole) as [[Hiy Hty] _].
    change (Rmin (snd (init (reconnect_one l sub r h s))) (snd (term (reconnect_one l sub r h s))) <= snd p <=
      Rmax (snd (init (reconnect_one l sub r h s))) (snd (term (reconnect_one l sub r h s)))) in Hpy.
    rewrite Hinit, Hterm in Hpy.
    unfold ReconnectByClassifier.operate_point in Hpy. rewrite Hi, Ht in Hpy. simpl in Hpy.
    pose proof (in_sub_rect_or_endpoints_bbox_y sub p Hne (proj1 Htarget)) as Hbounds.
    unfold Rmin, Rmax in Hpy. destruct Rle_dec; lra.
  - assert (Ht : classifier l sub r (term s) = RegFix) by congruence.
    destruct (uniformly_reconnected_triangle_preimage l sub r h s p RegFix
      Hspec Hh Hwhole Hi Ht Hp) as [old [Hold Heq]].
    simpl in Heq. subst p.
    destruct (pmp_triangle_meeting_moves_up l sub r Hspec s old Hin Hold Htarget) as [Hup _].
    congruence.
Qed.

(* 固定された延長線なら旧三角形接触に、Up なら sub の固定と
   延長線・本体の上下順序に矛盾させる。 *)
Lemma pmp_shifted_extension_avoids_triangle : forall l sub r h p q g,
  sub <> [] -> connected sub ->
  @ReconnectClassificationSpec l sub r (classifier l sub r) -> h_large h sub ->
  (onHead_extend_strict (l ++ sub ++ r) q \/ onLast_extend_strict (l ++ sub ++ r) q) ->
  (g = RegUp \/ g = RegFix) ->
  (g = RegFix -> ~ in_sub_triangle Plus sub q) ->
  (g = RegUp -> forall z, onSegmentlist sub z ->
    fst q = fst z -> snd q < snd z -> False) ->
  p = shift h g q -> ~ in_sub_triangle Plus sub p.
Proof.
  intros l sub r h p q g Hne Hconn Hspec Hh Hext [Hg | Hg] Hfix Hup Hshift Htarget.
  - subst g.
    eapply (ReconnectLocalByClassifier.classified_shifted_extension_avoids_sub_rect_from_spec
      classifier l sub r h p q RegUp Hne Hconn Hspec Hh Hext); try exact (proj1 Htarget).
    + intros _ z Hz Hx Hy. exfalso. exact (Hup eq_refl z Hz Hx Hy).
    + discriminate.
    + intros. now left.
    + exact Hshift.
  - subst g. simpl in Hshift. subst p. exact (Hfix eq_refl Htarget).
Qed.

Lemma pmp_reconnect_extensions_avoid_triangle : forall l sub r h,
  sub <> [] -> connected sub ->
  @PMPClassificationSpec l sub r (classifier l sub r) ->
  h_large h sub -> sparse_embedding (l ++ sub ++ r) ->
  forall p,
    ((l <> [] /\ onHead_extend_strict (reconnect_whole l sub r h) p) \/
     (r <> [] /\ onLast_extend_strict (reconnect_whole l sub r h) p)) ->
    ~ in_sub_triangle Plus sub p.
Proof.
  intros l sub r h Hne Hconn Hspec Hh Hsparse p [[Hl Hhead] | [Hr Hlast]].
  - destruct (ReconnectLocalByClassifier.reconnect_head_strict_extension_preimage_from_spec
      classifier l sub r h p Hne Hsparse Hspec (Rlt_le _ _ (proj1 Hh)) Hhead)
      as [q [Hq Hshift]].
    eapply (pmp_shifted_extension_avoids_triangle l sub r h p q
      (classifier l sub r (init (hd_segment (l ++ sub ++ r)))));
      try eassumption; try exact (pmp_reconnect_spec l sub r Hspec).
    + now left.
    + exact (pmp_only_up_or_fix l sub r Hspec _).
    + intros Hfix Htarget. pose proof (pmp_head_meeting_moves_up l sub r Hspec Hl q Hq Htarget).
      congruence.
    + intros Hup z [s [Hs Hon]] Hx Hy.
      assert (Hin : In s (l ++ sub ++ r)) by (rewrite !in_app_iff; tauto).
      destruct (proj1 (classified_head_segment_crossing_order l sub r Hspec s z q Hin Hon Hq ltac:(symmetry; exact Hx)) Hy)
        as [Horder _].
      rewrite Hup in Horder. apply region_at_or_above_RegUp_inv in Horder.
      pose proof (classified_sub_fixed l sub r Hspec (init s)
        (ex_intro _ s (conj Hs (onInit s)))). congruence.
  - destruct (ReconnectLocalByClassifier.reconnect_last_strict_extension_preimage_from_spec
      classifier l sub r h p Hne Hsparse Hspec (Rlt_le _ _ (proj1 Hh)) Hlast)
      as [q [Hq Hshift]].
    eapply (pmp_shifted_extension_avoids_triangle l sub r h p q
      (classifier l sub r (term (last_segment (l ++ sub ++ r)))));
      try eassumption; try exact (pmp_reconnect_spec l sub r Hspec).
    + now right.
    + exact (pmp_only_up_or_fix l sub r Hspec _).
    + intros Hfix Htarget. pose proof (pmp_last_meeting_moves_up l sub r Hspec Hr q Hq Htarget).
      congruence.
    + intros Hup z [s [Hs Hon]] Hx Hy.
      assert (Hin : In s (l ++ sub ++ r)) by (rewrite !in_app_iff; tauto).
      destruct (proj1 (classified_last_segment_crossing_order l sub r Hspec s z q Hin Hon Hq ltac:(symmetry; exact Hx)) Hy)
        as [Horder _].
      rewrite Hup in Horder. apply region_at_or_above_RegUp_inv in Horder.
      pose proof (classified_sub_fixed l sub r Hspec (init s)
        (ex_intro _ s (conj Hs (onInit s)))). congruence.
Qed.

(* 全域保存とは独立に、PMP 用の入力仕様から局所三角形退避を導く。 *)
Lemma pmp_reconnect_gives_sparse_around : forall l sub r h,
  sub <> [] -> connected sub ->
  @PMPClassificationSpec l sub r (classifier l sub r) ->
  h_large h sub -> height_clears_sub h l sub r ->
  sparse_embedding (l ++ sub ++ r) ->
  sparse_around_triangle Plus
    (reconnect_segs l sub r h l) sub (reconnect_segs l sub r h r).
Proof.
  intros l sub r h Hne Hconn Hspec Hh Hclear Hsparse. split.
  - intros p [[Hl Hon] | [Hr Hon]];
      eapply pmp_reconnect_extensions_avoid_triangle; try eassumption.
    + left. split; [|exact Hon]. intros Hnil. apply Hl.
      unfold ReconnectByClassifier.reconnect_segs. now rewrite Hnil.
    + right. split; [|exact Hon]. intros Hnil. apply Hr.
      unfold ReconnectByClassifier.reconnect_segs. now rewrite Hnil.
  - intros s' p Hs' Hp. unfold ReconnectByClassifier.reconnect_segs in Hs'.
    rewrite nonadjacent_sides_map in Hs'. apply in_map_iff in Hs'.
    destruct Hs' as [s [Heq Hin]]. subst s'.
    eapply pmp_reconnect_one_avoids_triangle; eauto.
Qed.
End TriangleClearance.

(* 共通の三つの保存定理と、上方向だけの三角形退避を合成する。
   sub 自身は再接続しないので、簡約用の端点・傾き条件も変わらない。 *)
Lemma embed_sparsely_PMP_prepared_from_spec :
  forall classifier ds1 ds2 l sub r,
    PreparedPMPEmbedding ds1 ds2 l sub r ->
    @PMPClassificationSpec l sub r (classifier l sub r) ->
    exists l' r',
      embed_listDir ds1 l' /\ embed_listDir [Plus; Minus; Plus] sub /\
      embed_listDir ds2 r' /\
      embed_listDir (ds1 ++ [Plus; Minus; Plus] ++ ds2) (l' ++ sub ++ r') /\
      sparse_embedding (l' ++ sub ++ r') /\ ~ close (l' ++ sub ++ r') /\
      sparse_around_triangle Plus l' sub r'.
Proof.
  intros classifier ds1 ds2 l sub r Hprepared Hspec.
  destruct Hprepared as [Hl Hsub Hr Hwhole Hsparse Hext HnoT Hslope].
  pose proof (embedding_listDir_length_consis _ _ Hsub) as HlenSub.
  assert (Hne : sub <> []).
  { intros Hnil. rewrite Hnil in HlenSub. discriminate. }
  destruct (choose_height_clearing_sub l sub r) as [h [Hh Hclear]].
  set (l' := ReconnectByClassifier.reconnect_segs classifier l sub r h l).
  set (r' := ReconnectByClassifier.reconnect_segs classifier l sub r h r).
  assert (Hwhole' : embed_listDir (ds1 ++ [Plus; Minus; Plus] ++ ds2) (l' ++ sub ++ r')).
  { exact (ReconnectLocalByClassifier.prepared_reconnect_whole_preserves_embed
      classifier _ l sub r h Hne Hspec Hh Hsparse Hwhole Hext). }
  assert (HlenL : length ds1 = length l').
  { unfold l'. rewrite ReconnectLocalByClassifier.reconnect_segs_length.
    exact (embedding_listDir_length_consis _ _ Hl). }
  destruct (embed_listDir_split_known ds1 ([Plus; Minus; Plus] ++ ds2)
    l' (sub ++ r') Hwhole' HlenL) as [Hl' Htail].
  pose proof (proj2 (embed_listDir_split_known [Plus; Minus; Plus] ds2 sub r' Htail HlenSub)) as Hr'.
  assert (Hsparse' : sparse_embedding (l' ++ sub ++ r')).
  { exact (ReconnectWholeByClassifier.reconnect_preserves_sparse_embedding_from_spec
      classifier _ l sub r h Hne Hspec Hh Hsparse Hwhole Hext). }
  assert (Hext' : extensions_disjoint (l' ++ sub ++ r')).
  { exact (ReconnectWholeByClassifier.ordinary_extensions_disjoint_prepared
      classifier _ l sub r h Hne Hspec Hh Hsparse Hwhole Hext). }
  assert (HnewNe : l' ++ sub ++ r' <> []).
  { intros Hnil. apply app_eq_nil in Hnil as [_ Hnil].
    apply app_eq_nil in Hnil as [Hnil _]. contradiction. }
  assert (Hopen : ~ close (l' ++ sub ++ r')).
  { exact (sparse_extensions_open _ _ HnewNe Hwhole' Hsparse' Hext'). }
  assert (Hconn : connected sub).
  { eapply connected_middle. exact (embed_listDir_connected _ _ Hwhole). }
  assert (Haround : sparse_around_triangle Plus l' sub r').
  { exact (pmp_reconnect_gives_sparse_around classifier l sub r h
      Hne Hconn Hspec Hh Hclear Hsparse). }
  exists l', r'.
  split; [exact Hl' |]. split; [exact Hsub |]. split; [exact Hr' |].
  split; [exact Hwhole' |]. split; [exact Hsparse' |].
  split; [exact Hopen | exact Haround].
Qed.
