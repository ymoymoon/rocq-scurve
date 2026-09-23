Require Import Admissible.
Require Import Reduction.
Require Import Stdlib.Reals.Reals.
Require Import Embed.
Require Import PrimitiveSegment.
Require Import Segment.
Require Import SegmentsTranslation.
Require Import ListExt.
Require Import Stdlib.Logic.ClassicalDescription.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.



Require Export Classify.
(* ================================================================= *)
(*  1.  AdmissibleDirs について成り立ってほしい性質と，それに必要な補題   *)
(* ================================================================= *)

(* 単方向曲線と向き列が同じなら単方向曲線 *) 
Lemma is_one_way_same_direction : forall sc1 sc2,
	scurve_to_direction sc1 = scurve_to_direction sc2
	-> is_one_way_scurve sc1 
	-> is_one_way_scurve sc2.
Proof.	
Admitted.

Lemma Direction_to_PrimitiveSegment : forall d p, exists p', orn p' = d /\ dc p p'.
Proof.
	intros d p.
	destruct d; destruct p as [[v h] c];
	destruct v; destruct h; destruct c; eexists;
	(* split; try apply DXtrvN. reflexivity. *)
	try solve [split; try apply DIfl; reflexivity];
	try solve [split; try apply DXtrvN; reflexivity];
	try solve [split; try apply DXtrvS; reflexivity];
	try solve [split; try apply DXtrhN; reflexivity];
	try solve [split; try apply DXtrhS; reflexivity].
Qed.

(* 向きの列と先頭の PrimitiveSegment の組に対し，対応する scurve が(1つ)定まる *)
Lemma direction_scurve_correspondence : forall ds p,
	exists sc, hd_scurve sc = p /\ scurve_to_direction sc = orn p :: ds.
Proof.
	intros ds.
	induction ds as [ | d ds' IH]; intros p.
	- (* ds = [] *) exists (scurve_from_one p). split; reflexivity.
	- (* ds = d :: ds' *) 
		(* 向き d を持ち，p と直接連結可能な PrimitiveSegment p' をとる *)
		pose proof (Direction_to_PrimitiveSegment d p) as [p' [Horn_p' Hdc]].
		(* IH より，先頭 p' で向き orn p' :: ds' の scurve がとれる *)
		destruct (IH p') as [sc [Hhead Hdir]].
		assert (H0: exists l, proj1_sig sc = p' :: l). {
			unfold scurve_to_direction in Hdir. 
			unfold hd_scurve in Hhead. 
			destruct (proj1_sig sc) as [| p0 l0].
			- discriminate.
			- simpl in Hhead; subst. exists l0. reflexivity.
		}
		destruct H0 as [l H0].
		pose (DcCons _ _ l Hdc) as H1.
		rewrite <- H0 in H1.
		(* p :: (proj1_sig sc) が求める scurve *)
		exists (connect p sc H1). split.
		+ (* 先頭の条件 *) auto.
		+ (* 向きの条件 *) unfold scurve_to_direction. simpl.
			unfold scurve_to_direction in Hdir. rewrite Hdir. rewrite Horn_p'. reflexivity.
Qed.

(* 向き列の許容可能性を調べることで，scurve の許容可能性はわかる．
	(つまり１つの scurve で許容可能性が言えたら，同じ向き列を持つ他の scurve ４つの許容可能性もわかる) *)
Lemma admissible_AdmissibleDirs_correspondence : forall sc,
	admissible sc <-> AdmissibleDirs (scurve_to_direction sc).
Proof. 
	intros sc. split.
	- intros adms ps Hps.
	  (* ps が空なら自明，そうでなければ先頭の Primitive Segment の向きとして４通り考えられ，
			内１つは ps = sc を導く．それ以外の場合は，sc の開埋め込みを90度ずつ回転させることで ps の開埋め込みとなる． *)
          symmetry in Hps. destruct (rot_scurve_of_same_direction _ _ Hps) as [g ->].
          now rewrite <- rot_scurve_admissible.
	- auto.
Qed.

(* 向きが ds の許容可能な scurve を見つけることと，向きが ds である任意の scurve が許容可能であることは同値 *)
Lemma AdmissibleDirs_exist : forall ds,
	AdmissibleDirs ds <-> exists sc, scurve_to_direction sc = ds /\ admissible sc.
Proof.
	intros ds. split.
	- (* -> *) intros H.
		destruct ds as [ | d tail].
		+ (* ds = [] *) exists (exist _ _ IsScurveNil). auto.
		+ (* ds = d :: tail *) 
			pose proof (Direction_to_PrimitiveSegment d default_primitive_segment) as [p [H0 _]].
			pose proof (direction_scurve_correspondence tail p) as [sc [H1 H2]].
			exists sc. split; try apply H; subst; assumption.
	- (* <- *) intros [sc [Hdir Hadm]].
			rewrite <- Hdir.
			apply admissible_AdmissibleDirs_correspondence.
			assumption.
Qed.

Lemma admissible_gives_open_embed :
  forall ds, AdmissibleDirs ds -> exists ls, embed_listDir ds ls /\ ~ close ls.
Proof.
  intros ds Hadm.
  apply AdmissibleDirs_exist in Hadm.
  destruct Hadm as [sc [Hdir Hadm]].
  destruct Hadm as [ls [Hembed Hopen]].
  exists ls.
  split; auto.
  exists sc.
  split; auto.
Qed.


(* ================================================================= *)
(*  2.  端点移動後の再接続                                           *)
(* ================================================================= *)

Definition reconnectable_after
  (l sub r : list Segment) (h : R) (s : Segment) : Prop :=
  reconnectable
    (operate_point l sub r h (init s))
    (operate_point l sub r h (term s))
    (orn_seg s).

Definition reconnect_slope_after
  (l sub r : list Segment) (h : R) (s : Segment) : Prop :=
  reconnect_slope
    (operate_point l sub r h (init s))
    (operate_point l sub r h (term s))
    (orn_seg s) (slope_init s) (slope_term s).

Definition reconnect_init_slope_after
  (l sub r : list Segment) (h : R) (s : Segment) : Prop :=
  reconnect_init_slope
    (operate_point l sub r h (init s))
    (operate_point l sub r h (term s))
    (orn_seg s) (slope_init s).

Definition reconnect_term_slope_after
  (l sub r : list Segment) (h : R) (s : Segment) : Prop :=
  reconnect_term_slope
    (operate_point l sub r h (init s))
    (operate_point l sub r h (term s))
    (orn_seg s) (slope_term s).

Definition head_init_slope_after
  (l sub r : list Segment) (h : R) (s : Segment) : Prop :=
  l <> [] /\ s = hd_segment l /\ reconnect_init_slope_after l sub r h s.

Definition last_term_slope_after
  (l sub r : list Segment) (h : R) (s : Segment) : Prop :=
  r <> [] /\ s = last_segment r /\ reconnect_term_slope_after l sub r h s.

Definition all_reconnectable
  (l sub r : list Segment) (h : R) (ls : list Segment) : Prop :=
  forall s, In s ls -> reconnectable_after l sub r h s.

Definition reconnect_one
  (l sub r : list Segment) (h : R) (s : Segment) : Segment :=
  match excluded_middle_informative (reconnectable_after l sub r h s) with
  | left H =>
      match excluded_middle_informative
              (reconnect_slope_after l sub r h s) with
      | left Hs => make_seg_slope
          (operate_point l sub r h (init s))
          (operate_point l sub r h (term s))
          (orn_seg s) (slope_init s) (slope_term s) Hs
      | right _ =>
          match excluded_middle_informative
                  (head_init_slope_after l sub r h s) with
          | left Hs => make_seg_init_slope
              (operate_point l sub r h (init s))
              (operate_point l sub r h (term s))
              (orn_seg s) (slope_init s) (proj2 (proj2 Hs))
          | right _ =>
              match excluded_middle_informative
                      (last_term_slope_after l sub r h s) with
              | left Hs => make_seg_term_slope
                  (operate_point l sub r h (init s))
                  (operate_point l sub r h (term s))
                  (orn_seg s) (slope_term s) (proj2 (proj2 Hs))
              | right _ => make_seg
                  (operate_point l sub r h (init s))
                  (operate_point l sub r h (term s))
                  (orn_seg s) H
              end
          end
      end
  | right _ => default_segment
  end.

Definition reconnect_segs
  (l sub r : list Segment) (h : R) (ls : list Segment) : list Segment :=
  map (reconnect_one l sub r h) ls.

(* sub 自体は変更せず、左右の全端点だけを移動して再接続する。 *)
Definition reconnect_split
  (l sub r : list Segment) (h : R) : list Segment :=
  reconnect_segs l sub r h l ++ sub ++ reconnect_segs l sub r h r.

(* 再接続の三つの基本仕様は、同じ場合分けを一度だけ行って得る。 *)
Lemma reconnect_one_endpoints_orn :
  forall l sub r h s,
    reconnectable_after l sub r h s ->
    init (reconnect_one l sub r h s) = operate_point l sub r h (init s)
    /\ term (reconnect_one l sub r h s) = operate_point l sub r h (term s)
    /\ orn_seg (reconnect_one l sub r h s) = orn_seg s.
Proof.
  intros l sub r h s Hrec. unfold reconnect_one.
  destruct (excluded_middle_informative
              (reconnectable_after l sub r h s)) as [H | H].
  - destruct (excluded_middle_informative
                (reconnect_slope_after l sub r h s)) as [Hs | Hs].
    + pose proof (make_seg_slope_spec _ _ _ _ _ Hs) as [Hi [Ht [Ho _]]].
      now repeat split.
    + destruct (excluded_middle_informative
                  (head_init_slope_after l sub r h s)) as [Hi | Hi].
      * pose proof (make_seg_init_slope_spec
          _ _ _ _ (proj2 (proj2 Hi))) as [Hinit [Hterm [Horn _]]].
        now repeat split.
      * destruct (excluded_middle_informative
                    (last_term_slope_after l sub r h s)) as [Ht | Ht].
        -- pose proof (make_seg_term_slope_spec
             _ _ _ _ (proj2 (proj2 Ht))) as [Hinit [Hterm [Horn _]]].
           now repeat split.
        -- repeat split; [apply make_seg_init | apply make_seg_term | apply make_seg_orn].
  - contradiction.
Qed.

Lemma reconnect_one_init :
  forall l sub r h s,
    reconnectable_after l sub r h s ->
    init (reconnect_one l sub r h s) = operate_point l sub r h (init s).
Proof.
  intros l sub r h s Hrec.
  exact (proj1 (reconnect_one_endpoints_orn l sub r h s Hrec)).
Qed.

Lemma reconnect_one_term :
  forall l sub r h s,
    reconnectable_after l sub r h s ->
    term (reconnect_one l sub r h s) = operate_point l sub r h (term s).
Proof.
  intros l sub r h s Hrec.
  exact (proj1 (proj2 (reconnect_one_endpoints_orn l sub r h s Hrec))).
Qed.

Lemma reconnect_one_orn :
  forall l sub r h s,
    reconnectable_after l sub r h s ->
    orn_seg (reconnect_one l sub r h s) = orn_seg s.
Proof.
  intros l sub r h s Hrec.
  exact (proj2 (proj2 (reconnect_one_endpoints_orn l sub r h s Hrec))).
Qed.

Lemma reconnect_slope_after_init :
  forall l sub r h s,
    reconnect_slope_after l sub r h s ->
    reconnect_init_slope_after l sub r h s.
Proof.
  intros l sub r h s Hslope.
  unfold reconnect_slope_after, reconnect_init_slope_after,
    reconnect_init_slope.
  now exists (slope_term s).
Qed.

Lemma reconnect_slope_after_term :
  forall l sub r h s,
    reconnect_slope_after l sub r h s ->
    reconnect_term_slope_after l sub r h s.
Proof.
  intros l sub r h s Hslope.
  unfold reconnect_slope_after, reconnect_term_slope_after,
    reconnect_term_slope.
  now exists (slope_init s).
Qed.

(* 先頭として選ばれた再接続は、片側の存在条件だけで始点傾きを保存する。 *)
Lemma reconnect_one_head_slope_init :
  forall l sub r h s,
    l <> [] ->
    s = hd_segment l ->
    reconnect_init_slope_after l sub r h s ->
    slope_init (reconnect_one l sub r h s) = slope_init s.
Proof.
  intros l sub r h s Hl Hhead Hslope. unfold reconnect_one.
  destruct (excluded_middle_informative
              (reconnectable_after l sub r h s)) as [Hrec | Hrec].
  - destruct (excluded_middle_informative
                (reconnect_slope_after l sub r h s)) as [Hs | Hs].
    + exact (proj1 (proj2 (proj2 (proj2
        (make_seg_slope_spec _ _ _ _ _ Hs))))).
    + destruct (excluded_middle_informative
                  (head_init_slope_after l sub r h s)) as [Hi | Hi].
      * exact (proj2 (proj2 (proj2
          (make_seg_init_slope_spec _ _ _ _ (proj2 (proj2 Hi)))))).
      * exfalso. apply Hi. repeat split; assumption.
  - exfalso. apply Hrec. unfold reconnectable_after.
    unfold reconnect_init_slope_after in Hslope.
    now apply reconnect_init_slope_reconnectable with
      (slope_p := slope_init s).
Qed.

(* 先頭用分岐と競合しない末尾は、片側の存在条件だけで終点傾きを保存する。 *)
Lemma reconnect_one_last_slope_term :
  forall l sub r h s,
    ~ head_init_slope_after l sub r h s ->
    r <> [] ->
    s = last_segment r ->
    reconnect_term_slope_after l sub r h s ->
    slope_term (reconnect_one l sub r h s) = slope_term s.
Proof.
  intros l sub r h s HnotHead Hr Hlast Hslope. unfold reconnect_one.
  destruct (excluded_middle_informative
              (reconnectable_after l sub r h s)) as [Hrec | Hrec].
  - destruct (excluded_middle_informative
                (reconnect_slope_after l sub r h s)) as [Hs | Hs].
    + exact (proj2 (proj2 (proj2 (proj2
        (make_seg_slope_spec _ _ _ _ _ Hs))))).
    + destruct (excluded_middle_informative
                  (head_init_slope_after l sub r h s)) as [Hi | Hi].
      * contradiction.
      * destruct (excluded_middle_informative
                    (last_term_slope_after l sub r h s)) as [Ht | Ht].
        -- exact (proj2 (proj2 (proj2
            (make_seg_term_slope_spec _ _ _ _ (proj2 (proj2 Ht)))))).
        -- exfalso. apply Ht. repeat split; assumption.
  - exfalso. apply Hrec. unfold reconnectable_after.
    unfold reconnect_term_slope_after in Hslope.
    now apply reconnect_term_slope_reconnectable with
      (slope_q := slope_term s).
Qed.

(* 両端点が同じ領域なら、元のセグメントの平行移動が傾き付き再接続を与える。 *)
Lemma same_region_reconnect_slope_after :
  forall l sub r h s,
    classify l sub r (init s) = classify l sub r (term s) ->
    reconnect_slope_after l sub r h s.
Proof.
  intros l sub r h s Hregion. unfold reconnect_slope_after.
  apply (proj2 (reconnect_slope_spec _ _ _ _ _)).
  exists (translate_seg
            (region_translation h (classify l sub r (init s))) s).
  repeat split.
  - rewrite translate_seg_init. unfold operate_point.
    now rewrite shift_as_translation.
  - rewrite translate_seg_term. unfold operate_point.
    rewrite <- Hregion. now rewrite shift_as_translation.
  - apply translate_seg_orn.
  - apply translate_seg_slope_init.
  - apply translate_seg_slope_term.
Qed.

(* 始点を Up にする場合、終点の移動を差し引くと始点だけを上げる変形になる。 *)
Lemma raised_init_reconnect_slope_after :
  forall l sub r h seg,
    0 <= h ->
    classify l sub r (init seg) = RegUp ->
    (forall p,
      fst p = fst (init seg) ->
      snd (init seg) <= snd p ->
      reconnect_init_slope
        p (term seg) (orn_seg seg) (slope_init seg)) ->
    reconnect_init_slope_after l sub r h seg.
Proof.
  intros l sub r h seg Hh Hregion Hraise.
  set (g := classify l sub r (term seg)).
  set (v := region_translation h g).
  set (p0 := translate_pt (opposite_translation v)
               (shift h RegUp (init seg))).
  assert (Hx : fst p0 = fst (init seg)).
  { unfold p0, v, opposite_translation, translate_pt, region_translation,
      shift. destruct g; destruct (init seg); simpl; ring. }
  assert (Hy : snd (init seg) <= snd p0).
  { unfold p0, v, opposite_translation, translate_pt, region_translation,
      shift. destruct g; destruct (init seg); simpl; lra. }
  pose proof (Hraise p0 Hx Hy) as Hbase.
  pose proof (reconnect_init_slope_translate
                v p0 (term seg) (orn_seg seg) (slope_init seg) Hbase)
    as Htranslated.
  assert (Hp : translate_pt v p0 = shift h RegUp (init seg)).
  { unfold p0. apply translate_pt_opposite_left. }
  assert (Hq : translate_pt v (term seg) = shift h g (term seg)).
  { unfold v. symmetry. apply shift_as_translation. }
  unfold reconnect_init_slope_after, operate_point. rewrite Hregion.
  change (reconnect_init_slope
            (shift h RegUp (init seg)) (shift h g (term seg))
            (orn_seg seg) (slope_init seg)).
  now rewrite <- Hp, <- Hq.
Qed.

(* 始点を Down にする場合は、同様に始点だけを下げる変形へ帰着する。 *)
Lemma lowered_init_reconnect_slope_after :
  forall l sub r h seg,
    0 <= h ->
    classify l sub r (init seg) = RegDown ->
    (forall p,
      fst p = fst (init seg) ->
      snd p <= snd (init seg) ->
      reconnect_init_slope
        p (term seg) (orn_seg seg) (slope_init seg)) ->
    reconnect_init_slope_after l sub r h seg.
Proof.
  intros l sub r h seg Hh Hregion Hlower.
  set (g := classify l sub r (term seg)).
  set (v := region_translation h g).
  set (p0 := translate_pt (opposite_translation v)
               (shift h RegDown (init seg))).
  assert (Hx : fst p0 = fst (init seg)).
  { unfold p0, v, opposite_translation, translate_pt, region_translation,
      shift. destruct g; destruct (init seg); simpl; ring. }
  assert (Hy : snd p0 <= snd (init seg)).
  { unfold p0, v, opposite_translation, translate_pt, region_translation,
      shift. destruct g; destruct (init seg); simpl; lra. }
  pose proof (Hlower p0 Hx Hy) as Hbase.
  pose proof (reconnect_init_slope_translate
                v p0 (term seg) (orn_seg seg) (slope_init seg) Hbase)
    as Htranslated.
  assert (Hp : translate_pt v p0 = shift h RegDown (init seg)).
  { unfold p0. apply translate_pt_opposite_left. }
  assert (Hq : translate_pt v (term seg) = shift h g (term seg)).
  { unfold v. symmetry. apply shift_as_translation. }
  unfold reconnect_init_slope_after, operate_point. rewrite Hregion.
  change (reconnect_init_slope
            (shift h RegDown (init seg)) (shift h g (term seg))
            (orn_seg seg) (slope_init seg)).
  now rewrite <- Hp, <- Hq.
Qed.

(* 終点側についても、始点の移動を差し引いて片端変形へ帰着する。 *)
Lemma raised_term_reconnect_slope_after :
  forall l sub r h seg,
    0 <= h ->
    classify l sub r (term seg) = RegUp ->
    (forall p,
      fst p = fst (term seg) ->
      snd (term seg) <= snd p ->
      reconnect_term_slope
        (init seg) p (orn_seg seg) (slope_term seg)) ->
    reconnect_term_slope_after l sub r h seg.
Proof.
  intros l sub r h seg Hh Hregion Hraise.
  set (g := classify l sub r (init seg)).
  set (v := region_translation h g).
  set (q0 := translate_pt (opposite_translation v)
               (shift h RegUp (term seg))).
  assert (Hx : fst q0 = fst (term seg)).
  { unfold q0, v, opposite_translation, translate_pt, region_translation,
      shift. destruct g; destruct (term seg); simpl; ring. }
  assert (Hy : snd (term seg) <= snd q0).
  { unfold q0, v, opposite_translation, translate_pt, region_translation,
      shift. destruct g; destruct (term seg); simpl; lra. }
  pose proof (Hraise q0 Hx Hy) as Hbase.
  pose proof (reconnect_term_slope_translate
                v (init seg) q0 (orn_seg seg) (slope_term seg) Hbase)
    as Htranslated.
  assert (Hp : translate_pt v (init seg) = shift h g (init seg)).
  { unfold v. symmetry. apply shift_as_translation. }
  assert (Hq : translate_pt v q0 = shift h RegUp (term seg)).
  { unfold q0. apply translate_pt_opposite_left. }
  unfold reconnect_term_slope_after, operate_point. rewrite Hregion.
  change (reconnect_term_slope
            (shift h g (init seg)) (shift h RegUp (term seg))
            (orn_seg seg) (slope_term seg)).
  now rewrite <- Hp, <- Hq.
Qed.

Lemma lowered_term_reconnect_slope_after :
  forall l sub r h seg,
    0 <= h ->
    classify l sub r (term seg) = RegDown ->
    (forall p,
      fst p = fst (term seg) ->
      snd p <= snd (term seg) ->
      reconnect_term_slope
        (init seg) p (orn_seg seg) (slope_term seg)) ->
    reconnect_term_slope_after l sub r h seg.
Proof.
  intros l sub r h seg Hh Hregion Hlower.
  set (g := classify l sub r (init seg)).
  set (v := region_translation h g).
  set (q0 := translate_pt (opposite_translation v)
               (shift h RegDown (term seg))).
  assert (Hx : fst q0 = fst (term seg)).
  { unfold q0, v, opposite_translation, translate_pt, region_translation,
      shift. destruct g; destruct (term seg); simpl; ring. }
  assert (Hy : snd q0 <= snd (term seg)).
  { unfold q0, v, opposite_translation, translate_pt, region_translation,
      shift. destruct g; destruct (term seg); simpl; lra. }
  pose proof (Hlower q0 Hx Hy) as Hbase.
  pose proof (reconnect_term_slope_translate
                v (init seg) q0 (orn_seg seg) (slope_term seg) Hbase)
    as Htranslated.
  assert (Hp : translate_pt v (init seg) = shift h g (init seg)).
  { unfold v. symmetry. apply shift_as_translation. }
  assert (Hq : translate_pt v q0 = shift h RegDown (term seg)).
  { unfold q0. apply translate_pt_opposite_left. }
  unfold reconnect_term_slope_after, operate_point. rewrite Hregion.
  change (reconnect_term_slope
            (shift h g (init seg)) (shift h RegDown (term seg))
            (orn_seg seg) (slope_term seg)).
  now rewrite <- Hp, <- Hq.
Qed.

(* 東向きの sub に西向きから直接つながる先頭は、dc の水平反転二場合に限られる。 *)
Lemma singleton_head_before_x_monotone_sub_shape :
  forall ds seg sub r,
    sub <> [] ->
    x_monotone_segs sub ->
    embed_listDir ds ([seg] ++ sub ++ r) ->
    fst (init (hd_segment sub)) < fst (init seg) ->
    (embed (n, w, cc) seg /\ embed (n, e, cx) (hd_segment sub))
    \/ (embed (s, w, cx) seg /\ embed (s, e, cc) (hd_segment sub)).
Proof.
  intros ds s0 sub r Hne Hmono [sc [_ Hembed]] Hx.
  destruct sub as [|t sub']; [contradiction|].
  simpl in Hx |- *.
  assert (Hxt : x_monotone_seg t).
  { apply Hmono. now left. }
  destruct (embed_scurve_adjacent_data
              sc (s0 :: t :: sub' ++ r) 0 s0 t Hembed
              ltac:(reflexivity) ltac:(reflexivity))
    as [ps1 [ps2 [Hembed1 [Hembed2 [Hdc Hjoin]]]]].
  destruct Hdc; destruct h.
  - pose proof (e_end_relation s0 v c Hembed1).
    rewrite Hjoin in H. unfold x_monotone_seg, init_x, term_x in Hxt. lra.
  - pose proof (w_end_relation t v (i_c c) Hembed2).
    unfold x_monotone_seg, init_x, term_x in Hxt. lra.
  - pose proof (e_end_relation s0 n cx Hembed1).
    rewrite Hjoin in H. lra.
  - pose proof (w_end_relation t s cx Hembed2).
    unfold x_monotone_seg, init_x, term_x in Hxt. lra.
  - pose proof (e_end_relation s0 s cc Hembed1).
    rewrite Hjoin in H. lra.
  - pose proof (w_end_relation t n cc Hembed2).
    unfold x_monotone_seg, init_x, term_x in Hxt. lra.
  - pose proof (e_end_relation s0 n cc Hembed1).
    rewrite Hjoin in H. lra.
  - left. now split.
  - pose proof (e_end_relation s0 s cx Hembed1).
    rewrite Hjoin in H. lra.
  - right. now split.
Qed.

(* 東向きの sub から西向きへ直接つながる末尾も、dc の水平反転二場合に限られる。 *)
Lemma singleton_last_after_x_monotone_sub_shape :
  forall ds l sub seg,
    sub <> [] ->
    x_monotone_segs sub ->
    embed_listDir ds (l ++ sub ++ [seg]) ->
    fst (term seg) < fst (term (last_segment sub)) ->
    (embed (n, e, cc) (last_segment sub) /\ embed (n, w, cx) seg)
    \/ (embed (s, e, cx) (last_segment sub) /\ embed (s, w, cc) seg).
Proof.
  intros ds l sub s0 Hne Hmono [sc [_ Hembed]] Hx.
  assert (HsubPos : (0 < length sub)%nat).
  { destruct (length sub) eqn:Hlen; [|lia].
    apply length_zero_iff_nil in Hlen. contradiction. }
  set (i := (length l + length sub - 1)%nat).
  assert (HsubLast :
      nth_error (l ++ sub ++ [s0]) i = Some (last_segment sub)).
  { unfold i. rewrite nth_error_app2 by lia.
    replace (length l + length sub - 1 - length l)%nat
      with (length sub - 1)%nat by lia.
    rewrite nth_error_app1.
    - apply nth_error_last. exact Hne.
    - apply Nat.sub_lt; lia. }
  assert (Hs0 : nth_error (l ++ sub ++ [s0]) (S i) = Some s0).
  { unfold i. rewrite nth_error_app2 by lia.
    replace (S (length l + length sub - 1) - length l)%nat
      with (length sub)%nat by lia.
    rewrite nth_error_app2 by lia.
    now replace (length sub - length sub)%nat with 0%nat by lia. }
  destruct (embed_scurve_adjacent_data
              sc (l ++ sub ++ [s0]) i (last_segment sub) s0
              Hembed HsubLast Hs0)
    as [ps1 [ps2 [Hembed1 [Hembed2 [Hdc Hjoin]]]]].
  rewrite Hjoin in Hx.
  assert (Hxt : x_monotone_seg (last_segment sub)).
  { apply Hmono. apply last_In. exact Hne. }
  destruct Hdc; destruct h.
  - pose proof (e_end_relation s0 v (i_c c) Hembed2). lra.
  - pose proof (w_end_relation (last_segment sub) v c Hembed1).
    unfold x_monotone_seg, init_x, term_x in Hxt. lra.
  - pose proof (e_end_relation s0 s cx Hembed2). lra.
  - pose proof (w_end_relation (last_segment sub) n cx Hembed1).
    unfold x_monotone_seg, init_x, term_x in Hxt. lra.
  - pose proof (e_end_relation s0 n cc Hembed2). lra.
  - pose proof (w_end_relation (last_segment sub) s cc Hembed1).
    unfold x_monotone_seg, init_x, term_x in Hxt. lra.
  - left. now split.
  - pose proof (w_end_relation (last_segment sub) n cc Hembed1).
    unfold x_monotone_seg, init_x, term_x in Hxt. lra.
  - right. now split.
  - pose proof (w_end_relation (last_segment sub) s cx Hembed1).
    unfold x_monotone_seg, init_x, term_x in Hxt. lra.
Qed.

(* sub を挟む先頭と末尾は非隣接なので、疎性により同じセグメントではない。 *)
Lemma sparse_head_last_distinct_across_sub :
  forall l sub r,
    l <> [] -> sub <> [] -> r <> [] ->
    sparse_embedding (l ++ sub ++ r) ->
    hd_segment l <> last_segment r.
Proof.
  intros [|a l'] [|b sub'] [|c r'] Hl Hsub Hr Hsparse;
    try contradiction.
  simpl. intro Heq.
  destruct (Hsparse [] a (l' ++ b :: sub' ++ c :: r') ltac:(reflexivity))
    as [_ Hrect].
  assert (HinR : In (last_segment (c :: r')) (c :: r')).
  { apply last_In. discriminate. }
  assert (Hin :
      In (last_segment (c :: r'))
        (nonadjacent_sides [] (l' ++ b :: sub' ++ c :: r'))).
  { unfold nonadjacent_sides. simpl.
    destruct l' as [|d l'']; simpl.
    - apply in_or_app. right. exact HinR.
    - apply in_or_app. right. simpl. right.
      apply in_or_app. right. exact HinR. }
  specialize (Hrect (last_segment (c :: r')) (init a) Hin).
  apply Hrect.
  - rewrite <- Heq. now apply segment_in_rect_or_endpoints, onInit.
  - change (in_segment_rect_or_endpoints a (init a)).
    now apply segment_in_rect_or_endpoints, onInit.
Qed.

(* sub 側の端点だけを固定する先頭の特例では、延長線に必要な始点傾きだけを指定する。 *)
Lemma reconnect_head_fixed_endpoint_slope :
  forall ds l sub r h s,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    0 <= h ->
    l = [s] ->
    fst (init (hd_segment sub)) < fst (init s) ->
    reconnect_init_slope_after l sub r h (hd_segment l).
Proof.
  intros ds l sub r h s0 Hne Hconn Hmono Hsparse Hembed Hh Hl Hx.
  subst l. simpl in *.
  assert (Hwhole : connected ([s0] ++ sub ++ r)).
  { change (connected (s0 :: sub ++ r)).
    exact (embed_listDir_connected ds (s0 :: sub ++ r) Hembed). }
  assert (Hterm : term s0 = init (hd_segment sub)).
  { apply (embed_listDir_connected ds ([s0] ++ sub ++ r) Hembed 0%nat s0
             (hd_segment sub)); [reflexivity |].
    destruct sub; [contradiction | reflexivity]. }
  assert (HtermFix : classify [s0] sub r (term s0) = RegFix).
  { rewrite Hterm.
    exact (classified_sub_fixed
             [s0] sub r
             (classify_spec [s0] sub r Hne Hconn Hmono Hsparse Hwhole)
             (init (hd_segment sub))
             (onSegmentlist_init_hd sub Hne)). }
  destruct (singleton_head_before_x_monotone_sub_shape
              ds s0 sub r Hne Hmono Hembed Hx)
    as [[Hnorth _] | [Hsouth _]].
  - pose proof (n_end_relation s0 w cc Hnorth) as Hy.
    pose proof (proj1 (classified_segment_endpoints_monotone
                         [s0] sub r
                         (classify_spec [s0] sub r Hne Hconn Hmono Hsparse Hwhole)
                         s0 ltac:(simpl; auto)) Hy) as Horder.
    destruct (classify [s0] sub r (init s0)) eqn:HinitRegion.
    + apply reconnect_slope_after_init.
      apply same_region_reconnect_slope_after. now rewrite HtermFix.
    + rewrite HtermFix in Horder.
      destruct Horder as [Heq | Habove]; [discriminate | inversion Habove].
    + assert (Hlower :
          snd (shift h RegDown (init s0)) <= snd (init s0)).
      { destruct (init s0). simpl. lra. }
      unfold reconnect_init_slope_after, operate_point.
      rewrite HinitRegion, HtermFix. simpl.
      apply northwest_cc_lower_init_slope;
        [exact Hnorth | reflexivity | exact Hlower].
  - pose proof (s_end_relation s0 w cx Hsouth) as Hy.
    pose proof (proj2 (classified_segment_endpoints_monotone
                         [s0] sub r
                         (classify_spec [s0] sub r Hne Hconn Hmono Hsparse Hwhole)
                         s0 ltac:(simpl; auto)) Hy) as Horder.
    destruct (classify [s0] sub r (init s0)) eqn:HinitRegion.
    + apply reconnect_slope_after_init.
      apply same_region_reconnect_slope_after. now rewrite HtermFix.
    + assert (Hraise :
          snd (init s0) <= snd (shift h RegUp (init s0))).
      { destruct (init s0). simpl. lra. }
      unfold reconnect_init_slope_after, operate_point.
      rewrite HinitRegion, HtermFix. simpl.
      apply southwest_cx_raise_init_slope;
        [exact Hsouth | reflexivity | exact Hraise].
    + rewrite HtermFix in Horder.
      destruct Horder as [Heq | Habove]; [discriminate | inversion Habove].
Qed.

(* sub 側の端点だけを固定する末尾の特例。 *)
Lemma reconnect_last_fixed_endpoint_slope :
  forall ds l sub r h s,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    0 <= h ->
    r = [s] ->
    fst (term s) < fst (term (last_segment sub)) ->
    reconnect_term_slope_after l sub r h (last_segment r).
Proof.
  intros ds l sub r h s0 Hne Hconn Hmono Hsparse Hembed Hh Hr Hx.
  subst r. simpl in *.
  destruct Hembed as [sc [Hdir Hcurve]].
  assert (HembedList : embed_listDir ds (l ++ sub ++ [s0])).
  { exists sc. now split. }
  assert (Hwhole : connected (l ++ sub ++ [s0])).
  { exact (embed_listDir_connected ds (l ++ sub ++ [s0]) HembedList). }
  assert (Hinit : init s0 = term (last_segment sub)).
  { symmetry.
    assert (Hcurve' : embed_scurve sc ((l ++ sub) ++ [s0])).
    { rewrite <- app_assoc. exact Hcurve. }
    pose proof (consist_init_term
                  sc (l ++ sub) [s0] Hcurve'
                  ltac:(intro Hnil; apply app_eq_nil in Hnil as [_ Hsub]; contradiction)
                  ltac:(discriminate)) as Hjoin.
    simpl in Hjoin.
    change (term (last_segment (l ++ sub)) = init s0) in Hjoin.
    rewrite last_app_nonnil in Hjoin by exact Hne. exact Hjoin. }
  assert (HinitFix : classify l sub [s0] (init s0) = RegFix).
  { rewrite Hinit.
    exact (classified_sub_fixed
             l sub [s0]
             (classify_spec l sub [s0] Hne Hconn Hmono Hsparse Hwhole)
             (term (last_segment sub))
             (onSegmentlist_term_last sub Hne)). }
  destruct (singleton_last_after_x_monotone_sub_shape
              ds l sub s0 Hne Hmono HembedList Hx)
    as [[_ Hnorth] | [_ Hsouth]].
  - pose proof (n_end_relation s0 w cx Hnorth) as Hy.
    pose proof (proj1 (classified_segment_endpoints_monotone
                         l sub [s0]
                         (classify_spec l sub [s0] Hne Hconn Hmono Hsparse Hwhole)
                         s0 ltac:(rewrite !in_app_iff; simpl; auto)) Hy) as Horder.
    destruct (classify l sub [s0] (term s0)) eqn:HtermRegion.
    + apply reconnect_slope_after_term.
      apply same_region_reconnect_slope_after.
      change (classify l sub [s0] (init s0) =
              classify l sub [s0] (term s0)). congruence.
    + assert (Hraise :
          snd (term s0) <= snd (shift h RegUp (term s0))).
      { destruct (term s0). simpl. lra. }
      change (reconnect_term_slope
                (shift h (classify l sub [s0] (init s0)) (init s0))
                (shift h (classify l sub [s0] (term s0)) (term s0))
                (orn_seg s0) (slope_term s0)).
      rewrite HinitFix, HtermRegion. simpl.
      apply northwest_cx_raise_term_slope;
        [exact Hnorth | reflexivity | exact Hraise].
    + rewrite HinitFix in Horder.
      destruct Horder as [Heq | Habove]; [discriminate | inversion Habove].
  - pose proof (s_end_relation s0 w cc Hsouth) as Hy.
    pose proof (proj2 (classified_segment_endpoints_monotone
                         l sub [s0]
                         (classify_spec l sub [s0] Hne Hconn Hmono Hsparse Hwhole)
                         s0 ltac:(rewrite !in_app_iff; simpl; auto)) Hy) as Horder.
    destruct (classify l sub [s0] (term s0)) eqn:HtermRegion.
    + apply reconnect_slope_after_term.
      apply same_region_reconnect_slope_after.
      change (classify l sub [s0] (init s0) =
              classify l sub [s0] (term s0)). congruence.
    + rewrite HinitFix in Horder.
      destruct Horder as [Heq | Habove]; [discriminate | inversion Habove].
    + assert (Hlower :
          snd (shift h RegDown (term s0)) <= snd (term s0)).
      { destruct (term s0). simpl. lra. }
      change (reconnect_term_slope
                (shift h (classify l sub [s0] (init s0)) (init s0))
                (shift h (classify l sub [s0] (term s0)) (term s0))
                (orn_seg s0) (slope_term s0)).
      rewrite HinitFix, HtermRegion. simpl.
      apply southwest_cc_lower_term_slope;
        [exact Hsouth | reflexivity | exact Hlower].
Qed.

Lemma reconnect_head_init_slope_after :
  forall ds l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    0 <= h ->
    l <> [] ->
    reconnect_init_slope_after l sub r h (hd_segment l).
Proof.
  intros ds l sub r h Hne Hconn Hmono Hsparse Hembed Hh Hl.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  destruct (classified_head_slope_case
              l sub r
              (classify_spec l sub r Hne Hconn Hmono Hsparse Hwhole) Hl)
    as [Hsame | [[Hup [Hsw | Hse]] | [Hdown [Hnw | Hneast]]]].
  - apply reconnect_slope_after_init.
    now apply same_region_reconnect_slope_after.
  - eapply raised_init_reconnect_slope_after; [exact Hh | exact Hup |].
    intros p Hx Hy. now apply southwest_cx_raise_init_slope.
  - eapply raised_init_reconnect_slope_after; [exact Hh | exact Hup |].
    intros p Hx Hy. now apply southeast_cx_raise_init_slope.
  - eapply lowered_init_reconnect_slope_after; [exact Hh | exact Hdown |].
    intros p Hx Hy. now apply northwest_cc_lower_init_slope.
  - eapply lowered_init_reconnect_slope_after; [exact Hh | exact Hdown |].
    intros p Hx Hy. now apply northeast_cc_lower_init_slope.
Qed.

Lemma reconnect_last_term_slope_after :
  forall ds l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    0 <= h ->
    r <> [] ->
    reconnect_term_slope_after l sub r h (last_segment r).
Proof.
  intros ds l sub r h Hne Hconn Hmono Hsparse Hembed Hh Hr.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  destruct (classified_last_slope_case
              l sub r
              (classify_spec l sub r Hne Hconn Hmono Hsparse Hwhole) Hr)
    as [Hsame | [[Hup [Hnw | Hneast]] | [Hdown [Hsw | Hse]]]].
  - apply reconnect_slope_after_term.
    now apply same_region_reconnect_slope_after.
  - eapply raised_term_reconnect_slope_after; [exact Hh | exact Hup |].
    intros p Hx Hy. now apply northwest_cx_raise_term_slope.
  - eapply raised_term_reconnect_slope_after; [exact Hh | exact Hup |].
    intros p Hx Hy. now apply northeast_cx_raise_term_slope.
  - eapply lowered_term_reconnect_slope_after; [exact Hh | exact Hdown |].
    intros p Hx Hy. now apply southwest_cc_lower_term_slope.
  - eapply lowered_term_reconnect_slope_after; [exact Hh | exact Hdown |].
    intros p Hx Hy. now apply southeast_cc_lower_term_slope.
Qed.

(* 傾きを保存した再接続の始端延長線点を，移動前へ戻す。 *)
Lemma reconnect_one_head_extension_preimage :
  forall l sub r h s p,
    l <> [] ->
    s = hd_segment l ->
    reconnect_init_slope_after l sub r h s ->
    onHead (reconnect_one l sub r h s) p ->
    exists q,
      onHead s q
      /\ p = shift h (classify l sub r (init s)) q.
Proof.
  intros l sub r h s p Hl Hhead Hslope Hp.
  assert (Hrec : reconnectable_after l sub r h s).
  { unfold reconnectable_after.
    unfold reconnect_init_slope_after in Hslope.
    now apply reconnect_init_slope_reconnectable with
      (slope_p := slope_init s). }
  set (v := region_translation h (classify l sub r (init s))).
  assert (Hinit :
    init (reconnect_one l sub r h s) = init (translate_seg v s)).
  { rewrite reconnect_one_init by exact Hrec.
    rewrite translate_seg_init. unfold operate_point, v.
    now rewrite shift_as_translation. }
  assert (HslopeEq :
    slope_init (reconnect_one l sub r h s) =
    slope_init (translate_seg v s)).
  { rewrite (reconnect_one_head_slope_init _ _ _ _ _ Hl Hhead Hslope).
    symmetry. apply translate_seg_slope_init. }
  pose proof (proj1
    (head_extension_determined_by_init_slope
       (reconnect_one l sub r h s) (translate_seg v s)
       Hinit HslopeEq p) Hp) as Htranslated.
  destruct Htranslated as [t [Ht Hpoint]].
  exists (point s t). split.
  - exists t. split; [exact Ht | reflexivity].
  - rewrite shift_as_translation. unfold v in Hpoint.
    rewrite translate_seg_point in Hpoint. simpl in Hpoint.
    symmetry. exact Hpoint.
Qed.

(* 傾き保存した再接続の終端延長線点の移動前の像。 *)
Lemma reconnect_one_last_extension_preimage :
  forall l sub r h s p,
    ~ head_init_slope_after l sub r h s ->
    r <> [] ->
    s = last_segment r ->
    reconnect_term_slope_after l sub r h s ->
    onLast (reconnect_one l sub r h s) p ->
    exists q,
      onLast s q
      /\ p = shift h (classify l sub r (term s)) q.
Proof.
  intros l sub r h s p HnotHead Hr Hlast Hslope Hp.
  assert (Hrec : reconnectable_after l sub r h s).
  { unfold reconnectable_after.
    unfold reconnect_term_slope_after in Hslope.
    now apply reconnect_term_slope_reconnectable with
      (slope_q := slope_term s). }
  set (v := region_translation h (classify l sub r (term s))).
  assert (Hterm :
    term (reconnect_one l sub r h s) = term (translate_seg v s)).
  { rewrite reconnect_one_term by exact Hrec.
    rewrite translate_seg_term. unfold operate_point, v.
    now rewrite shift_as_translation. }
  assert (HslopeEq :
    slope_term (reconnect_one l sub r h s) =
    slope_term (translate_seg v s)).
  { rewrite (reconnect_one_last_slope_term
               _ _ _ _ _ HnotHead Hr Hlast Hslope).
    symmetry. apply translate_seg_slope_term. }
  pose proof (proj1
    (last_extension_determined_by_term_slope
       (reconnect_one l sub r h s) (translate_seg v s)
       Hterm HslopeEq p) Hp) as Htranslated.
  destruct Htranslated as [t [Ht Hpoint]].
  exists (point s t). split.
  - exists t. split; [exact Ht | reflexivity].
  - rewrite shift_as_translation. unfold v in Hpoint.
    rewrite translate_seg_point in Hpoint. simpl in Hpoint.
    symmetry. exact Hpoint.
Qed.

(* 再接続後の先頭延長線は，旧先頭延長線の一律な上下移動である。 *)
Lemma reconnect_head_extension_preimage :
  forall l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (l <> [] -> reconnect_init_slope_after l sub r h (hd_segment l)) ->
    onHead_extend (reconnect_split l sub r h) p ->
    exists q,
      onHead_extend (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (init (hd_segment (l ++ sub ++ r)))) q.
Proof.
  intros l sub r h p Hne Hconn Hmono Hsparse Hwhole Hslope Hp.
  destruct l as [|a l'].
  - destruct sub as [|b sub']; [contradiction|].
    assert (Hfix : classify [] (b :: sub') r (init b) = RegFix).
    { apply (classified_sub_fixed
               [] (b :: sub') r
               (classify_spec [] (b :: sub') r
                  ltac:(discriminate) Hconn Hmono Hsparse Hwhole)).
      apply onSegmentlist_init_hd. discriminate. }
    exists p. split.
    + exact Hp.
    + simpl in Hfix |- *. now rewrite Hfix.
  - simpl in Hp |- *.
    apply (reconnect_one_head_extension_preimage
             (a :: l') sub r h a p).
    + discriminate.
    + reflexivity.
    + now apply Hslope; discriminate.
    + exact Hp.
Qed.

(* 再接続後の末尾延長線の移動前の像。 *)
Lemma reconnect_last_extension_preimage :
  forall l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (r <> [] -> reconnect_term_slope_after l sub r h (last_segment r)) ->
    onLast_extend (reconnect_split l sub r h) p ->
    exists q,
      onLast_extend (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (term (last_segment (l ++ sub ++ r)))) q.
Proof.
  intros l sub r h p Hne Hconn Hmono Hsparse Hwhole Hslope Hp.
  destruct r as [|a r'].
  - assert (HoldLast : last_segment (l ++ sub ++ []) = last_segment sub).
    { rewrite app_nil_r. apply last_app_nonnil. exact Hne. }
    assert (HnewLast :
      last_segment (reconnect_split l sub [] h) = last_segment sub).
    { unfold reconnect_split, reconnect_segs. simpl. rewrite app_nil_r.
      apply last_app_nonnil. exact Hne. }
    assert (Hfix : classify l sub [] (term (last_segment sub)) = RegFix).
    { apply (classified_sub_fixed
               l sub []
               (classify_spec l sub [] Hne Hconn Hmono Hsparse Hwhole)).
      apply onSegmentlist_term_last. exact Hne. }
    exists p. split.
    + unfold onLast_extend in *. now rewrite HnewLast in Hp; rewrite HoldLast.
    + rewrite HoldLast, Hfix. reflexivity.
  - assert (HoldLast :
      last_segment (l ++ sub ++ a :: r') = last_segment (a :: r')).
    { assert (Htail : sub ++ a :: r' <> []) by
        (destruct sub; discriminate).
      rewrite (last_app_nonnil l (sub ++ a :: r')) by exact Htail.
      apply last_app_nonnil. discriminate. }
    assert (HnewLast :
      last_segment (reconnect_split l sub (a :: r') h) =
      reconnect_one l sub (a :: r') h (last_segment (a :: r'))).
    { unfold reconnect_split, reconnect_segs.
      assert (Hmap : map (reconnect_one l sub (a :: r') h) (a :: r') <> [])
        by discriminate.
      assert (Htail :
        sub ++ map (reconnect_one l sub (a :: r') h) (a :: r') <> []) by
        (destruct sub; discriminate).
      rewrite (last_app_nonnil
                 (map (reconnect_one l sub (a :: r') h) l)
                 (sub ++ map (reconnect_one l sub (a :: r') h) (a :: r')))
        by exact Htail.
      rewrite (last_app_nonnil sub
                 (map (reconnect_one l sub (a :: r') h) (a :: r')))
        by exact Hmap.
      apply last_map_nonnil. discriminate. }
    unfold onLast_extend in Hp |- *.
    rewrite HnewLast in Hp. rewrite HoldLast.
    apply (reconnect_one_last_extension_preimage
             l sub (a :: r') h (last_segment (a :: r')) p).
    + unfold head_init_slope_after. intros [Hl [Heq _]].
      pose proof (sparse_head_last_distinct_across_sub
                    l sub (a :: r') Hl Hne ltac:(discriminate) Hsparse)
        as Hdistinct.
      apply Hdistinct. now symmetry.
    + discriminate.
    + reflexivity.
    + now apply Hslope; discriminate.
    + exact Hp.
Qed.

(* 再接続後の strict 先頭延長線点は，移動前の strict
   延長線点を先頭の分類どおりに動かしたものである。 *)
Lemma reconnect_head_strict_extension_preimage :
  forall ds l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    0 <= h ->
    onHead_extend_strict (reconnect_split l sub r h) p ->
    exists q,
      onHead_extend_strict (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (init (hd_segment (l ++ sub ++ r)))) q.
Proof.
  intros ds l sub r h p Hne Hconn Hmono Hsparse Hembed Hh Hstrict.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  destruct l as [|a l'].
  - destruct sub as [|b sub']; [contradiction|].
    assert (Hfix : classify [] (b :: sub') r (init b) = RegFix).
    { apply (classified_sub_fixed
               [] (b :: sub') r
               (classify_spec [] (b :: sub') r
                  ltac:(discriminate) Hconn Hmono Hsparse Hwhole)).
      apply onSegmentlist_init_hd. discriminate. }
    exists p. split.
    + exact Hstrict.
    + simpl in Hfix |- *. now rewrite Hfix.
  - simpl in Hstrict |- *.
    destruct Hstrict as [t [Ht Hpoint]].
    change (point (reconnect_one (a :: l') sub r h a) t = p) in Hpoint.
    pose proof (reconnect_head_init_slope_after
                  ds (a :: l') sub r h Hne Hconn Hmono Hsparse Hembed Hh
                  ltac:(discriminate)) as Hslope.
    simpl in Hslope.
    assert (Hrec : reconnectable_after (a :: l') sub r h a).
    { unfold reconnectable_after.
      unfold reconnect_init_slope_after in Hslope.
      now apply reconnect_init_slope_reconnectable with
        (slope_p := slope_init a). }
    set (v := region_translation h
                (classify (a :: l') sub r (init a))).
    assert (Hinit :
      init (reconnect_one (a :: l') sub r h a) =
      init (translate_seg v a)).
    { rewrite reconnect_one_init by exact Hrec.
      rewrite translate_seg_init. unfold operate_point, v.
      now rewrite shift_as_translation. }
    assert (HslopeEq :
      slope_init (reconnect_one (a :: l') sub r h a) =
      slope_init (translate_seg v a)).
    { rewrite (reconnect_one_head_slope_init
                 (a :: l') sub r h a ltac:(discriminate)
                 ltac:(reflexivity) Hslope).
      symmetry. apply translate_seg_slope_init. }
    assert (HonNew : onHead (reconnect_one (a :: l') sub r h a) p).
    { exists t. split; [lra | exact Hpoint]. }
    pose proof (proj1
      (head_extension_determined_by_init_slope
         (reconnect_one (a :: l') sub r h a)
         (translate_seg v a) Hinit HslopeEq p) HonNew) as HonTranslated.
    destruct HonTranslated as [u [Hu Htranslated]].
    assert (HuStrict : u < 0).
    { destruct (Req_dec u 0) as [Hu0 | Hu0]; [|lra].
      subst u.
      assert (Ht0 : t = 0).
      { apply (point_injective (reconnect_one (a :: l') sub r h a)).
        rewrite Hpoint.
        change (p = init (reconnect_one (a :: l') sub r h a)).
        rewrite Hinit.
        change (p = point (translate_seg v a) 0).
        symmetry. exact Htranslated. }
      lra. }
    exists (point a u). split.
    + exists u. split; [exact HuStrict | reflexivity].
    + rewrite shift_as_translation. unfold v in Htranslated.
      rewrite translate_seg_point in Htranslated. simpl in Htranslated.
      symmetry. exact Htranslated.
Qed.

(* 再接続後の strict 末尾延長線点の移動前の像。 *)
Lemma reconnect_last_strict_extension_preimage :
  forall ds l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    0 <= h ->
    onLast_extend_strict (reconnect_split l sub r h) p ->
    exists q,
      onLast_extend_strict (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (term (last_segment (l ++ sub ++ r)))) q.
Proof.
  intros ds l sub r h p Hne Hconn Hmono Hsparse Hembed Hh Hstrict.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  destruct r as [|a r'].
  - assert (HoldLast : last_segment (l ++ sub ++ []) = last_segment sub).
    { rewrite app_nil_r. apply last_app_nonnil. exact Hne. }
    assert (HnewLast :
      last_segment (reconnect_split l sub [] h) = last_segment sub).
    { unfold reconnect_split, reconnect_segs. simpl. rewrite app_nil_r.
      apply last_app_nonnil. exact Hne. }
    assert (Hfix : classify l sub [] (term (last_segment sub)) = RegFix).
    { apply (classified_sub_fixed
               l sub []
               (classify_spec l sub [] Hne Hconn Hmono Hsparse Hwhole)).
      apply onSegmentlist_term_last. exact Hne. }
    exists p. split.
    + unfold onLast_extend_strict in *. now rewrite HnewLast in Hstrict;
        rewrite HoldLast.
    + rewrite HoldLast, Hfix. reflexivity.
  - assert (HoldLast :
      last_segment (l ++ sub ++ a :: r') = last_segment (a :: r')).
    { assert (Htail : sub ++ a :: r' <> []).
      { destruct sub; discriminate. }
      rewrite (last_app_nonnil l (sub ++ a :: r')) by exact Htail.
      apply last_app_nonnil. discriminate. }
    assert (HnewLast :
      last_segment (reconnect_split l sub (a :: r') h) =
      reconnect_one l sub (a :: r') h (last_segment (a :: r'))).
    { unfold reconnect_split, reconnect_segs.
      assert (Hmap : map (reconnect_one l sub (a :: r') h) (a :: r') <> [])
        by discriminate.
      assert (Htail :
        sub ++ map (reconnect_one l sub (a :: r') h) (a :: r') <> []).
      { destruct sub; discriminate. }
      rewrite (last_app_nonnil
                 (map (reconnect_one l sub (a :: r') h) l)
                 (sub ++ map (reconnect_one l sub (a :: r') h) (a :: r')))
        by exact Htail.
      rewrite (last_app_nonnil sub
                 (map (reconnect_one l sub (a :: r') h) (a :: r')))
        by exact Hmap.
      apply last_map_nonnil. discriminate. }
    unfold onLast_extend_strict in Hstrict.
    rewrite HnewLast in Hstrict.
    destruct Hstrict as [t [Ht Hpoint]].
    pose proof (reconnect_last_term_slope_after
                  ds l sub (a :: r') h Hne Hconn Hmono Hsparse Hembed Hh
                  ltac:(discriminate)) as Hslope.
    set (s := last_segment (a :: r')).
    change (reconnect_term_slope_after l sub (a :: r') h s) in Hslope.
    change (point (reconnect_one l sub (a :: r') h s) t = p) in Hpoint.
    assert (Hrec : reconnectable_after l sub (a :: r') h s).
    { unfold reconnectable_after.
      unfold reconnect_term_slope_after in Hslope.
      now apply reconnect_term_slope_reconnectable with
        (slope_q := slope_term s). }
    assert (HnotHead : ~ head_init_slope_after l sub (a :: r') h s).
    { unfold head_init_slope_after. intros [Hl [Heq _]].
      pose proof (sparse_head_last_distinct_across_sub
                    l sub (a :: r') Hl Hne ltac:(discriminate) Hsparse)
        as Hdistinct.
      apply Hdistinct. unfold s in Heq. now symmetry. }
    set (v := region_translation h (classify l sub (a :: r') (term s))).
    assert (Hterm :
      term (reconnect_one l sub (a :: r') h s) =
      term (translate_seg v s)).
    { rewrite reconnect_one_term by exact Hrec.
      rewrite translate_seg_term. unfold operate_point, v.
      now rewrite shift_as_translation. }
    assert (HslopeEq :
      slope_term (reconnect_one l sub (a :: r') h s) =
      slope_term (translate_seg v s)).
    { rewrite (reconnect_one_last_slope_term
                 _ _ _ _ _ HnotHead ltac:(discriminate)
                 ltac:(reflexivity) Hslope).
      symmetry. apply translate_seg_slope_term. }
    assert (HonNew : onLast (reconnect_one l sub (a :: r') h s) p).
    { exists t. split; [lra | exact Hpoint]. }
    pose proof (proj1
      (last_extension_determined_by_term_slope
         (reconnect_one l sub (a :: r') h s)
         (translate_seg v s) Hterm HslopeEq p) HonNew) as HonTranslated.
    destruct HonTranslated as [u [Hu Htranslated]].
    assert (HuStrict : 1 < u).
    { destruct (Req_dec u 1) as [Hu1 | Hu1]; [|lra].
      subst u.
      assert (Ht1 : t = 1).
      { apply (point_injective (reconnect_one l sub (a :: r') h s)).
        rewrite Hpoint.
        change (p = term (reconnect_one l sub (a :: r') h s)).
        rewrite Hterm.
        change (p = point (translate_seg v s) 1).
        symmetry. exact Htranslated. }
      lra. }
    exists (point s u). split.
    + unfold onLast_extend_strict. rewrite HoldLast.
      change (exists u0, 1 < u0 /\ point s u0 = point s u).
      exists u. split; [exact HuStrict | reflexivity].
    + rewrite HoldLast. change (p = shift h (classify l sub (a :: r') (term s)) (point s u)).
      rewrite shift_as_translation. unfold v in Htranslated.
      rewrite translate_seg_point in Htranslated. simpl in Htranslated.
      symmetry. exact Htranslated.
Qed.

Lemma all_reconnectable_mono :
  forall l sub r h ls ls',
    all_reconnectable l sub r h ls ->
    (forall s, In s ls' -> In s ls) ->
    all_reconnectable l sub r h ls'.
Proof.
  intros l sub r h ls ls' Hrec Hin s Hs. apply Hrec, Hin, Hs.
Qed.

Lemma reconnect_segs_length :
  forall l sub r h ls,
    length (reconnect_segs l sub r h ls) = length ls.
Proof. intros. unfold reconnect_segs. apply length_map. Qed.

Lemma reconnect_segs_nth_error :
  forall l sub r h ls i s,
    nth_error ls i = Some s ->
    nth_error (reconnect_segs l sub r h ls) i =
      Some (reconnect_one l sub r h s).
Proof.
  intros l sub r h ls i s H. unfold reconnect_segs.
  rewrite nth_error_map, H. reflexivity.
Qed.

(* 同じ端点に同じ classify を適用するため、各部分列内部の連結性は保たれる。 *)
Lemma reconnect_segs_connected :
  forall l sub r h ls,
    all_reconnectable l sub r h ls ->
    connected ls ->
    connected (reconnect_segs l sub r h ls).
Proof.
  intros l sub r h ls Hrec Hc i s1 s2 H1 H2.
  unfold reconnect_segs in H1, H2.
  destruct (nth_error_map_inv _ _ _ _ H1) as [a [Ha Ea]].
  destruct (nth_error_map_inv _ _ _ _ H2) as [b [Hb Eb]].
  subst s1 s2.
  rewrite reconnect_one_term, reconnect_one_init.
  2,3: apply Hrec; eapply nth_error_In; eauto.
  f_equal. exact (Hc i a b Ha Hb).
Qed.

(* 再接続は各セグメントの向きと列の連結性を保つ。 *)
Lemma reconnect_preserves_embed :
  forall l sub r h ds ls,
    all_reconnectable l sub r h ls ->
    embed_listDir ds ls ->
    embed_listDir ds (reconnect_segs l sub r h ls).
Proof.
  intros l sub r h ds ls Hrec Hemb.
  eapply embed_scurve_transfer; [exact Hemb | | |].
  - apply reconnect_segs_length.
  - intros i s s' Hs Hs'.
    rewrite (reconnect_segs_nth_error l sub r h ls i s Hs) in Hs'.
    injection Hs' as Hs'. subst s'.
    apply reconnect_one_orn, Hrec. eapply nth_error_In; exact Hs.
  - eapply reconnect_segs_connected; [exact Hrec |].
    eapply embed_listDir_connected; exact Hemb.
Qed.


(* ================================================================= *)
(*  3.  疎性と延長線を保つ再接続                                     *)
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


(* ================================================================= *)
(*  4.  最終命題                                                     *)
(* ================================================================= *)

(* 許容可能なら，全てのセグメント周りで疎な埋め込みが取れる *)
Lemma AdmissibleDirs_has_sparse_embedding :
  forall ds,
    AdmissibleDirs ds ->
    exists ls,
      embed_listDir ds ls
      /\ sparse_embedding ls
      /\ extensions_disjoint ls.
Admitted.

(* 疎な埋め込みを回転して sub を x 単調にし、再接続で所望の疎性を得る。 *)
Lemma embed_sparsely_xmono :
  forall ds1 sub_ds ds2 l sub r,
    embed_listDir ds1 l -> embed_listDir sub_ds sub -> embed_listDir ds2 r ->
    embed_listDir (ds1 ++ sub_ds ++ ds2) (l ++ sub ++ r) ->
    well_split l sub r ->
    exists l' r' sub',
      embed_listDir ds1 l'
   /\ embed_listDir sub_ds sub'
   /\ embed_listDir ds2 r'
   /\ embed_listDir (ds1 ++ sub_ds ++ ds2) (l' ++ sub' ++ r')
   /\ ~ close (l' ++ sub' ++ r')
   /\ sparse_around l' sub' r'
   /\ sub' <> [].
Proof.
  intros ds1 sub_ds ds2 l sub r Hl Hsub Hr Hall Hws.
  pose proof Hws as [Hsubne [Hx Hopen]].
  assert (Hadm : AdmissibleDirs (ds1 ++ sub_ds ++ ds2)).
  { apply AdmissibleDirs_exist.
    destruct Hall as [sc [Hdir Hembed]].
    exists sc. split; [exact Hdir |].
    exists (l ++ sub ++ r). split; assumption. }
  destruct (AdmissibleDirs_has_sparse_embedding _ Hadm)
    as (ls0 & Hall0 & Hsparse & Hext).
  destruct (embed_split ds1 sub_ds ds2 ls0 Hall0)
    as (l0 & sub0 & r0 & Heq & Hl0 & Hsub0 & Hr0).
  subst ls0.
  assert (Hsub0ne : sub0 <> []).
  { intro Hnil.
    apply Hsubne.
    apply length_zero_iff_nil.
    pose proof (embedding_listDir_length_consis _ _ Hsub) as Hlen.
    pose proof (embedding_listDir_length_consis _ _ Hsub0) as Hlen0.
    rewrite Hnil in Hlen0. simpl in Hlen0. lia. }
  assert (HoneDir : is_one_way_listDir sub_ds).
  { eapply (x_monotone_embed_is_one_way_listDir sub_ds sub);
      [exact Hsub | exact Hx]. }
  assert (Hone0 : is_one_way_embedding sub0).
  { destruct Hsub0 as [sc0 [Hdir0 Hembed0]].
    destruct HoneDir as [sc [Hdir Hone]].
    exists sc0. split; [exact Hembed0 |].
    eapply is_one_way_same_direction; [| exact Hone].
    exact (eq_trans Hdir (eq_sym Hdir0)). }
  destruct (one_way_rot_exists sub0 Hone0) as [g Hx1].
  set (l1 := rot_segs g l0).
  set (sub1 := rot_segs g sub0).
  set (r1 := rot_segs g r0).
  assert (Hl1 : embed_listDir ds1 l1).
  { unfold l1. apply rot_embed. exact Hl0. }
  assert (Hsub1 : embed_listDir sub_ds sub1).
  { unfold sub1. apply rot_embed. exact Hsub0. }
  assert (Hr1 : embed_listDir ds2 r1).
  { unfold r1. apply rot_embed. exact Hr0. }
  assert (Hall1 :
      embed_listDir (ds1 ++ sub_ds ++ ds2) (l1 ++ sub1 ++ r1)).
  { unfold l1, sub1, r1. rewrite <- !rot_segs_app.
    apply rot_embed. exact Hall0. }
  assert (Hsparse1 : sparse_embedding (l1 ++ sub1 ++ r1)).
  { unfold l1, sub1, r1. rewrite <- !rot_segs_app.
    apply rot_sparse_embedding. exact Hsparse. }
  assert (Hext1 : extensions_disjoint (l1 ++ sub1 ++ r1)).
  { unfold l1, sub1, r1. rewrite <- !rot_segs_app.
    apply rot_extensions_disjoint. exact Hext. }
  assert (Hsub1ne : sub1 <> []).
  { unfold sub1. apply rot_segs_nonnil. exact Hsub0ne. }
  assert (Hopen1 : ~ close (l1 ++ sub1 ++ r1)).
  { eapply sparse_extensions_open with
      (ds := ds1 ++ sub_ds ++ ds2);
      [| exact Hall1 | exact Hsparse1 | exact Hext1].
    intro Hnil.
    apply app_eq_nil in Hnil as [_ Htail].
    apply app_eq_nil in Htail as [Hsubnil _].
    contradiction. }
  assert (Hws1 : well_split l1 sub1 r1).
  { split; [exact Hsub1ne |].
    split; [exact Hx1 | exact Hopen1]. }
  destruct (choose_h sub1) as [h Hh].
  assert (HconnAll1 : connected (l1 ++ sub1 ++ r1)).
  { eapply embed_listDir_connected. exact Hall1. }
  assert (HconnSub1 : connected sub1).
  { eapply connected_middle. exact HconnAll1. }
  pose proof (operate_endpoints_reconnectable
                l1 sub1 r1 h Hsub1ne HconnSub1 Hx1 Hh Hsparse1 HconnAll1)
    as HrecAll1.
  assert (HrecL1 : all_reconnectable l1 sub1 r1 h l1).
  { eapply all_reconnectable_mono; [exact HrecAll1 |].
    intros s Hs. rewrite !in_app_iff. auto. }
  assert (HrecR1 : all_reconnectable l1 sub1 r1 h r1).
  { eapply all_reconnectable_mono; [exact HrecAll1 |].
    intros s Hs. rewrite !in_app_iff. auto. }
  exists (reconnect_segs l1 sub1 r1 h l1),
         (reconnect_segs l1 sub1 r1 h r1),
         sub1.
  split; [apply reconnect_preserves_embed; assumption |].
  split; [exact Hsub1 |].
  split; [apply reconnect_preserves_embed; assumption |].
  split.
  - change (embed_listDir (ds1 ++ sub_ds ++ ds2)
              (reconnect_split l1 sub1 r1 h)).
    apply reconnect_split_preserves_embed; assumption.
  - split.
    + change (~ close (reconnect_split l1 sub1 r1 h)).
      assert (Hlocal : sparse_around
          (reconnect_segs l1 sub1 r1 h l1)
          sub1
          (reconnect_segs l1 sub1 r1 h r1)).
      { apply reconnect_gives_sparse_around with
          (ds := ds1 ++ sub_ds ++ ds2); assumption. }
      apply reconnect_preserves_open
        with (ds := ds1 ++ sub_ds ++ ds2).
      * exact Hh.
      * exact Hsub1ne.
      * exact Hx1.
      * exact HrecAll1.
      * exact Hall1.
      * exact Hsparse1.
      * exact Hext1.
      * exact Hlocal.
      * exact Hopen1.
    + split.
      * apply reconnect_gives_sparse_around with
          (ds := ds1 ++ sub_ds ++ ds2); assumption.
      * exact Hsub1ne.
Qed.

(* x 単調化した場合を逆回転し、一般の単方向部分列へ結果を輸送する。 *)
Proposition embed_sparsely_listDir (ds1 sub_ds ds2 : list Direction) :
  AdmissibleDirs (ds1 ++ sub_ds ++ ds2)
  -> is_one_way_listDir sub_ds
  -> exists l r sub_ls,
       embed_listDir ds1 l
    /\ embed_listDir sub_ds sub_ls
    /\ embed_listDir ds2 r
    /\ embed_listDir (ds1 ++ sub_ds ++ ds2) (l ++ sub_ls ++ r)
    /\ ~ close (l ++ sub_ls ++ r)
    /\ sparse_around l sub_ls r.
Proof.
  intros Hadm Hone.
  destruct (admissible_gives_open_embed _ Hadm) as [ls0 [Hemb0 Hopen0]].
  destruct (embed_split _ _ _ _ Hemb0)
    as (l0 & sub0 & r0 & Heq & Hl0 & Hsub0 & Hr0).
  subst ls0.

  assert (Hne : sub0 <> []).
  { eapply embed_nonnil; [exact Hsub0 | apply one_way_listDir_nonnil; exact Hone]. }

  assert (Honeway : is_one_way_embedding sub0).
  { destruct Hsub0 as [sc [Hdir Hembed]]. exists sc. split; [exact Hembed|].
    destruct Hone as [sc' [Hdir' Honeway]].
    apply (is_one_way_same_direction _ _ (eq_trans Hdir' (eq_sym Hdir)) Honeway). }

  destruct (one_way_rot_exists sub0 Honeway) as [g Hx].

  destruct (embed_sparsely_xmono
             ds1 sub_ds ds2
             (rot_segs g l0) (rot_segs g sub0) (rot_segs g r0))
    as (L & Rr & S & HL & HS & HR & Hallg & Hopeng & Hspg & HSne).
  { eapply rot_embed; exact Hl0. }
  { eapply rot_embed; exact Hsub0. }
  { eapply rot_embed; exact Hr0. }
  { rewrite <- !rot_segs_app.
    eapply rot_embed; exact Hemb0. }
  { split; [apply rot_segs_nonnil; exact Hne
           | split; [exact Hx
                    | rewrite <- !rot_segs_app; apply rot_open; exact Hopen0]]. }

  exists L, Rr, S.
  split; [exact HL |].
  split; [exact HS |].
  split; [exact HR |].
  split; [exact Hallg |].
  split; [exact Hopeng | exact Hspg].
Qed.
