Require Import Admissible.
Require Import Reduction.
Require Import Stdlib.Reals.Reals.
Require Import Embed.
Require Import PrimitiveSegment.
Require Import Segment.
Require Import SegmentsTranslation.
Require Import ListExt.
Require Import Stdlib.Logic.ClassicalDescription.
Require Import Stdlib.Logic.ClassicalEpsilon.
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

(* sub 自体は変更せず、左右の全端点だけを通常の方法で再接続する。
   安全な先頭・末尾を選ぶ最終的な [reconnect_split] の内部候補である。 *)
Definition ordinary_reconnect_split
  (l sub r : list Segment) (h : R) : list Segment :=
  reconnect_segs l sub r h l ++ sub ++ reconnect_segs l sub r h r.

(* 蓋かどうかは、sub 側へ x 方向に戻る位置関係だけで判定する。
   可能な向きと凸性は、後で隣接関係 [dc] から導く。 *)
Definition terminal_lid (l : list Segment) : Prop :=
  l <> [] /\
  fst (term (last_segment l)) < fst (init (last_segment l)).

Definition initial_lid (r : list Segment) : Prop :=
  r <> [] /\
  fst (term (hd_segment r)) < fst (init (hd_segment r)).

(* 西向きセグメントから東向きセグメントへの [dc] は、水平反転を
   行う二形に限られる。左右の蓋の形はこの事実から取り出す。 *)
Lemma west_to_east_dc_shapes :
  forall seg1 seg2 ps1 ps2,
    embed ps1 seg1 ->
    embed ps2 seg2 ->
    dc ps1 ps2 ->
    fst (term seg1) < fst (init seg1) ->
    fst (init seg2) < fst (term seg2) ->
    (embed (n, w, cc) seg1 \/ embed (s, w, cx) seg1)
    /\ (embed (n, e, cx) seg2 \/ embed (s, e, cc) seg2).
Proof.
  intros seg1 seg2 ps1 ps2 Hemb1 Hemb2 Hdc Hwest Heast.
  destruct Hdc; destruct h.
  - exfalso. pose proof (e_end_relation seg1 v c Hemb1). lra.
  - exfalso. pose proof (w_end_relation seg2 v (i_c c) Hemb2). lra.
  - exfalso. pose proof (e_end_relation seg1 n cx Hemb1). lra.
  - exfalso. pose proof (w_end_relation seg2 s cx Hemb2). lra.
  - exfalso. pose proof (e_end_relation seg1 s cc Hemb1). lra.
  - exfalso. pose proof (w_end_relation seg2 n cc Hemb2). lra.
  - exfalso. pose proof (e_end_relation seg1 n cc Hemb1). lra.
  - split; [now left | now left].
  - exfalso. pose proof (e_end_relation seg1 s cx Hemb1). lra.
  - split; [now right | now right].
Qed.

Lemma east_to_west_dc_shapes :
  forall seg1 seg2 ps1 ps2,
    embed ps1 seg1 ->
    embed ps2 seg2 ->
    dc ps1 ps2 ->
    fst (init seg1) < fst (term seg1) ->
    fst (term seg2) < fst (init seg2) ->
    (embed (n, e, cc) seg1 \/ embed (s, e, cx) seg1)
    /\ (embed (n, w, cx) seg2 \/ embed (s, w, cc) seg2).
Proof.
  intros seg1 seg2 ps1 ps2 Hemb1 Hemb2 Hdc Heast Hwest.
  destruct Hdc; destruct h.
  - exfalso. pose proof (e_end_relation seg2 v (i_c c) Hemb2). lra.
  - exfalso. pose proof (w_end_relation seg1 v c Hemb1). lra.
  - exfalso. pose proof (e_end_relation seg2 s cx Hemb2). lra.
  - exfalso. pose proof (w_end_relation seg1 n cx Hemb1). lra.
  - exfalso. pose proof (e_end_relation seg2 n cc Hemb2). lra.
  - exfalso. pose proof (w_end_relation seg1 s cc Hemb1). lra.
  - split; [now left | now left].
  - exfalso. pose proof (w_end_relation seg1 n cc Hemb1). lra.
  - split; [now right | now right].
  - exfalso. pose proof (w_end_relation seg1 s cx Hemb1). lra.
Qed.

(* 埋め込み列を二つに分けた境界では、左右の末尾・先頭に対応する
   PrimitiveSegment とその [dc] 証明を取り出せる。 *)
Lemma embed_listDir_app_boundary_data :
  forall ds left right,
    left <> [] ->
    right <> [] ->
    embed_listDir ds (left ++ right) ->
    exists ps1 ps2,
      embed ps1 (last_segment left)
      /\ embed ps2 (hd_segment right)
      /\ dc ps1 ps2
      /\ term (last_segment left) = init (hd_segment right).
Proof.
  intros ds left right Hleft Hright [sc [_ Hembed]].
  assert (Hlen : (0 < length left)%nat).
  { destruct left; [contradiction | simpl; lia]. }
  assert (Hlast :
      nth_error (left ++ right) (length left - 1) =
        Some (last_segment left)).
  { rewrite nth_error_app1 by lia.
    unfold last_segment. now apply nth_error_last. }
  assert (Hhead :
      nth_error (left ++ right) (S (length left - 1)) =
        Some (hd_segment right)).
  { replace (S (length left - 1)) with (length left) by lia.
    rewrite nth_error_app2 by lia.
    replace (length left - length left)%nat with 0%nat by lia.
    destruct right; [contradiction | reflexivity]. }
  exact (embed_scurve_adjacent_data
           sc (left ++ right) (length left - 1)
           (last_segment left) (hd_segment right)
           Hembed Hlast Hhead).
Qed.

(* 左側の戻り蓋の二形は、蓋判定には含めず、sub との [dc] から導く。 *)
Lemma terminal_lid_shape_from_dc :
  forall ds l sub r,
    sub <> [] ->
    x_monotone_segs sub ->
    embed_listDir ds (l ++ sub ++ r) ->
    terminal_lid l ->
    embed (n, w, cc) (last_segment l)
    \/ embed (s, w, cx) (last_segment l).
Proof.
  intros ds l sub r Hsub Hmono Hembed [Hl Hwest].
  assert (Htail : sub ++ r <> []) by (destruct sub; contradiction || discriminate).
  assert (Hembed' : embed_listDir ds (l ++ (sub ++ r))).
  { exact Hembed. }
  destruct (embed_listDir_app_boundary_data
              ds l (sub ++ r) Hl Htail Hembed')
    as [ps1 [ps2 [Hemb1 [Hemb2 [Hdc _]]]]].
  assert (Hhead : hd_segment (sub ++ r) = hd_segment sub).
  { symmetry. unfold hd_segment. now apply hd_app. }
  rewrite Hhead in Hemb2.
  assert (Heast : fst (init (hd_segment sub)) < fst (term (hd_segment sub))).
  { apply Hmono. destruct sub; [contradiction | now left]. }
  exact (proj1 (west_to_east_dc_shapes
                  (last_segment l) (hd_segment sub) ps1 ps2
                  Hemb1 Hemb2 Hdc Hwest Heast)).
Qed.

(* 右側の戻り蓋については、sub の末尾からの [dc] が双対の二形を与える。 *)
Lemma initial_lid_shape_from_dc :
  forall ds l sub r,
    sub <> [] ->
    x_monotone_segs sub ->
    embed_listDir ds (l ++ sub ++ r) ->
    initial_lid r ->
    embed (n, w, cx) (hd_segment r)
    \/ embed (s, w, cc) (hd_segment r).
Proof.
  intros ds l sub r Hsub Hmono Hembed [Hr Hwest].
  assert (Hprefix : l ++ sub <> []).
  { intros Hnil. apply app_eq_nil in Hnil as [_ Hnil]. contradiction. }
  assert (Hembed' : embed_listDir ds ((l ++ sub) ++ r)).
  { rewrite <- app_assoc. exact Hembed. }
  destruct (embed_listDir_app_boundary_data
              ds (l ++ sub) r Hprefix Hr Hembed')
    as [ps1 [ps2 [Hemb1 [Hemb2 [Hdc _]]]]].
  assert (Hlast : last_segment (l ++ sub) = last_segment sub).
  { now apply last_app_nonnil. }
  rewrite Hlast in Hemb1.
  assert (Heast : fst (init (last_segment sub)) < fst (term (last_segment sub))).
  { apply Hmono. apply last_In. exact Hsub. }
  exact (proj2 (east_to_west_dc_shapes
                  (last_segment sub) (hd_segment r) ps1 ps2
                  Hemb1 Hemb2 Hdc Heast Hwest)).
Qed.

Definition terminal_lid_blockers
    (l sub r : list Segment) (h : R) : list Segment :=
  nonadjacent_sides
    (removelast (reconnect_segs l sub r h l))
    (sub ++ reconnect_segs l sub r h r).

Definition initial_lid_blockers
    (l sub r : list Segment) (h : R) : list Segment :=
  nonadjacent_sides
    (reconnect_segs l sub r h l ++ sub)
    (tl (reconnect_segs l sub r h r)).

Definition terminal_lid_reconnect_spec
    (l sub r : list Segment) (h : R)
    (old : Segment) (blockers : list Segment) (new : Segment) : Prop :=
  reconnects_after l sub r h old new
  /\ slope_init new = slope_init old
  /\ segment_avoids_boxes new blockers.

Definition initial_lid_reconnect_spec
    (l sub r : list Segment) (h : R)
    (old : Segment) (blockers : list Segment) (new : Segment) : Prop :=
  reconnects_after l sub r h old new
  /\ slope_term new = slope_term old
  /\ segment_avoids_boxes new blockers.

(* sparse 性から得る安全な蓋を、epsilon で一つ選ぶ。 *)
Definition choose_terminal_lid
    (l sub r : list Segment) (h : R) : Segment :=
  epsilon (inhabits (reconnect_one l sub r h (last_segment l)))
    (terminal_lid_reconnect_spec l sub r h (last_segment l)
       (terminal_lid_blockers l sub r h)).

Definition choose_initial_lid
    (l sub r : list Segment) (h : R) : Segment :=
  epsilon (inhabits (reconnect_one l sub r h (hd_segment r)))
    (initial_lid_reconnect_spec l sub r h (hd_segment r)
       (initial_lid_blockers l sub r h)).

Definition reconnect_left
    (l sub r : list Segment) (h : R) : list Segment :=
  if excluded_middle_informative (terminal_lid l) then
    removelast (reconnect_segs l sub r h l) ++
      [choose_terminal_lid l sub r h]
  else reconnect_segs l sub r h l.

Definition reconnect_right
    (l sub r : list Segment) (h : R) : list Segment :=
  if excluded_middle_informative (initial_lid r) then
    choose_initial_lid l sub r h :: tl (reconnect_segs l sub r h r)
  else reconnect_segs l sub r h r.

(* 通常再接続の後、必要な場合だけ sub に隣接する二つの蓋を
   障害長方形を避ける証人へ置換する。sub 自体は変更しない。 *)
Definition reconnect_split
    (l sub r : list Segment) (h : R) : list Segment :=
  reconnect_left l sub r h ++ sub ++ reconnect_right l sub r h.

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

Lemma reconnect_head_init_slope_after :
  forall ds l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    0 <= h ->
    l <> [] ->
    reconnect_init_slope_after l sub r h (hd_segment l).
Proof.
  intros ds l sub r h Hne Hconn Hmono Hsparse Hembed Hext Hh Hl.
  unfold reconnect_init_slope_after, operate_point.
  exact (classified_head_init_slope_reconnectable
           l sub r
           (classify_spec l sub r Hne Hmono Hsparse
              (ex_intro _ ds Hembed) Hext)
           h Hh Hl).
Qed.

Lemma reconnect_last_term_slope_after :
  forall ds l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    0 <= h ->
    r <> [] ->
    reconnect_term_slope_after l sub r h (last_segment r).
Proof.
  intros ds l sub r h Hne Hconn Hmono Hsparse Hembed Hext Hh Hr.
  unfold reconnect_term_slope_after, operate_point.
  exact (classified_last_term_slope_reconnectable
           l sub r
           (classify_spec l sub r Hne Hmono Hsparse
              (ex_intro _ ds Hembed) Hext)
           h Hh Hr).
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
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    (l <> [] -> reconnect_init_slope_after l sub r h (hd_segment l)) ->
    onHead_extend (ordinary_reconnect_split l sub r h) p ->
    exists q,
      onHead_extend (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (init (hd_segment (l ++ sub ++ r)))) q.
Proof.
  intros l sub r h p Hne Hconn Hmono Hsparse Hwhole Hembedded Hext Hslope Hp.
  destruct l as [|a l'].
  - destruct sub as [|b sub']; [contradiction|].
    assert (Hfix : classify [] (b :: sub') r (init b) = RegFix).
    { apply (classified_sub_fixed
               [] (b :: sub') r
               (classify_spec [] (b :: sub') r
                  ltac:(discriminate) Hmono Hsparse Hembedded Hext)).
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
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    (r <> [] -> reconnect_term_slope_after l sub r h (last_segment r)) ->
    onLast_extend (ordinary_reconnect_split l sub r h) p ->
    exists q,
      onLast_extend (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (term (last_segment (l ++ sub ++ r)))) q.
Proof.
  intros l sub r h p Hne Hconn Hmono Hsparse Hwhole Hembedded Hext Hslope Hp.
  destruct r as [|a r'].
  - assert (HoldLast : last_segment (l ++ sub ++ []) = last_segment sub).
    { rewrite app_nil_r. apply last_app_nonnil. exact Hne. }
    assert (HnewLast :
      last_segment (ordinary_reconnect_split l sub [] h) = last_segment sub).
    { unfold ordinary_reconnect_split, reconnect_segs. simpl. rewrite app_nil_r.
      apply last_app_nonnil. exact Hne. }
    assert (Hfix : classify l sub [] (term (last_segment sub)) = RegFix).
    { apply (classified_sub_fixed
               l sub []
               (classify_spec l sub [] Hne Hmono Hsparse Hembedded Hext)).
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
      last_segment (ordinary_reconnect_split l sub (a :: r') h) =
      reconnect_one l sub (a :: r') h (last_segment (a :: r'))).
    { unfold ordinary_reconnect_split, reconnect_segs.
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
    extensions_disjoint (l ++ sub ++ r) ->
    0 <= h ->
    onHead_extend_strict (ordinary_reconnect_split l sub r h) p ->
    exists q,
      onHead_extend_strict (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (init (hd_segment (l ++ sub ++ r)))) q.
Proof.
  intros ds l sub r h p Hne Hconn Hmono Hsparse Hembed Hext Hh Hstrict.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  destruct l as [|a l'].
  - destruct sub as [|b sub']; [contradiction|].
    assert (Hfix : classify [] (b :: sub') r (init b) = RegFix).
    { apply (classified_sub_fixed
               [] (b :: sub') r
               (classify_spec [] (b :: sub') r
                  ltac:(discriminate) Hmono Hsparse
                  (ex_intro _ ds Hembed) Hext)).
      apply onSegmentlist_init_hd. discriminate. }
    exists p. split.
    + exact Hstrict.
    + simpl in Hfix |- *. now rewrite Hfix.
  - simpl in Hstrict |- *.
    destruct Hstrict as [t [Ht Hpoint]].
    change (point (reconnect_one (a :: l') sub r h a) t = p) in Hpoint.
    pose proof (reconnect_head_init_slope_after
                  ds (a :: l') sub r h Hne Hconn Hmono Hsparse Hembed Hext Hh
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
    extensions_disjoint (l ++ sub ++ r) ->
    0 <= h ->
    onLast_extend_strict (ordinary_reconnect_split l sub r h) p ->
    exists q,
      onLast_extend_strict (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (term (last_segment (l ++ sub ++ r)))) q.
Proof.
  intros ds l sub r h p Hne Hconn Hmono Hsparse Hembed Hext Hh Hstrict.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  destruct r as [|a r'].
  - assert (HoldLast : last_segment (l ++ sub ++ []) = last_segment sub).
    { rewrite app_nil_r. apply last_app_nonnil. exact Hne. }
    assert (HnewLast :
      last_segment (ordinary_reconnect_split l sub [] h) = last_segment sub).
    { unfold ordinary_reconnect_split, reconnect_segs. simpl. rewrite app_nil_r.
      apply last_app_nonnil. exact Hne. }
    assert (Hfix : classify l sub [] (term (last_segment sub)) = RegFix).
    { apply (classified_sub_fixed
               l sub []
               (classify_spec l sub [] Hne Hmono Hsparse
                  (ex_intro _ ds Hembed) Hext)).
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
      last_segment (ordinary_reconnect_split l sub (a :: r') h) =
      reconnect_one l sub (a :: r') h (last_segment (a :: r'))).
    { unfold ordinary_reconnect_split, reconnect_segs.
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
                  ds l sub (a :: r') h Hne Hconn Hmono Hsparse Hembed Hext Hh
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

(* map による再接続列は、各位置で分類後の端点と元の向きを共有する。 *)
Lemma reconnect_segs_reconnects_after :
  forall l sub r h ls,
    all_reconnectable l sub r h ls ->
    reconnects_list_after l sub r h ls (reconnect_segs l sub r h ls).
Proof.
  intros l sub r h ls Hrec.
  unfold reconnects_list_after.
  induction ls as [|s ls IH]; simpl.
  - constructor.
  - constructor.
    + unfold reconnects_after.
      exact (reconnect_one_endpoints_orn l sub r h s (Hrec s (or_introl eq_refl))).
    + apply IH. intros t Ht. apply Hrec. now right.
Qed.

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

(* sub に隣接する l 末尾より下の端点は、分類移動後にもその旧長方形
   より下に残る。隣接・非隣接の区別は不要である。 *)
Lemma operated_endpoint_below_terminal_stays_below :
  forall l sub r h p,
    sub <> [] ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    0 <= h ->
    l <> [] ->
    endpoint_of (l ++ sub ++ r) p ->
    snd p < ry0 (rect_of [last_segment l]) ->
    snd (operate_point l sub r h p) < ry0 (rect_of [last_segment l]).
Proof.
  intros l sub r h p Hne Hmono Hsparse Hembed Hext Hh Hl Hp Hbelow.
  unfold operate_point.
  pose proof (classified_below_terminal_not_up
                l sub r
                (classify_spec l sub r Hne Hmono Hsparse Hembed Hext)
                Hl p Hp Hbelow) as HnotUp.
  pose proof (shift_not_up_nonincreasing
                h (classify l sub r p) p Hh HnotUp).
  lra.
Qed.

(* r 先頭についての双対。 *)
Lemma operated_endpoint_below_initial_stays_below :
  forall l sub r h p,
    sub <> [] ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    0 <= h ->
    r <> [] ->
    endpoint_of (l ++ sub ++ r) p ->
    snd p < ry0 (rect_of [hd_segment r]) ->
    snd (operate_point l sub r h p) < ry0 (rect_of [hd_segment r]).
Proof.
  intros l sub r h p Hne Hmono Hsparse Hembed Hext Hh Hr Hp Hbelow.
  unfold operate_point.
  pose proof (classified_below_initial_not_up
                l sub r
                (classify_spec l sub r Hne Hmono Hsparse Hembed Hext)
                Hr p Hp Hbelow) as HnotUp.
  pose proof (shift_not_up_nonincreasing
                h (classify l sub r p) p Hh HnotUp).
  lra.
Qed.

(* 十分大きい移動では、各セグメントの二端点の y 座標は一致しない。 *)
Lemma operation_height_safe :
  forall l sub r h s,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    In s (l ++ sub ++ r) ->
    snd (operate_point l sub r h (init s)) <>
    snd (operate_point l sub r h (term s)).
Proof.
  intros l sub r h s Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hs.
  pose proof (classified_segment_endpoints_monotone
                l sub r
                (classify_spec l sub r Hne Hmono Hsparse Hembedded Hext)
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
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    In s (l ++ sub ++ r) ->
    reconnectable_after l sub r h s.
Proof.
  intros l sub r h s Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hs.
  unfold reconnectable_after, reconnectable. split.
  - rewrite !operate_point_fst. apply neq_init_term_x.
  - eapply operation_height_safe; eauto.
Qed.

Lemma operate_endpoints_reconnectable :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r).
Proof.
  intros l sub r h Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext s Hs.
  now apply (operate_one_endpoints_reconnectable
               l sub r h s Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext).
Qed.

(* 左蓋の移動後の二端点を、始点傾きを保ちつつ、通常再接続された
   非隣接セグメントの閉長方形を避けるように結べる。 *)
Lemma terminal_lid_safe_reconnect_exists :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    terminal_lid l ->
    exists s',
      terminal_lid_reconnect_spec l sub r h (last_segment l)
        (terminal_lid_blockers l sub r h) s'.
Admitted.

(* 右蓋についての双対。外側の末尾延長線に必要な終点傾きを保つ。 *)
Lemma initial_lid_safe_reconnect_exists :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    initial_lid r ->
    exists s',
      initial_lid_reconnect_spec l sub r h (hd_segment r)
        (initial_lid_blockers l sub r h) s'.
Admitted.

(* 安全な再接続の存在証明から、epsilon で選んだ左蓋の仕様を回収する。 *)
Lemma choose_terminal_lid_spec :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    terminal_lid l ->
    terminal_lid_reconnect_spec l sub r h (last_segment l)
      (terminal_lid_blockers l sub r h)
      (choose_terminal_lid l sub r h).
  Proof.
  intros l sub r h Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hlid.
  unfold choose_terminal_lid.
  apply epsilon_spec.
  eapply terminal_lid_safe_reconnect_exists; eauto.
Qed.

(* 右蓋についても、選択した証人は終点傾きと障害物回避を満たす。 *)
Lemma choose_initial_lid_spec :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    initial_lid r ->
    initial_lid_reconnect_spec l sub r h (hd_segment r)
      (initial_lid_blockers l sub r h)
      (choose_initial_lid l sub r h).
Proof.
  intros l sub r h Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hlid.
  unfold choose_initial_lid.
  apply epsilon_spec.
  eapply initial_lid_safe_reconnect_exists; eauto.
Qed.

Lemma removelast_length_nonempty : forall (A : Type) (xs : list A),
  xs <> [] -> S (length (removelast xs)) = length xs.
Proof.
  intros A xs. induction xs as [|x xs IH]; [contradiction |].
  destruct xs as [|y ys].
  - reflexivity.
  - simpl. intros _. specialize (IH ltac:(discriminate)). simpl in IH. lia.
Qed.

Lemma reconnect_left_length : forall l sub r h,
  length (reconnect_left l sub r h) = length l.
Proof.
  intros l sub r h. unfold reconnect_left.
  destruct (excluded_middle_informative (terminal_lid l)) as [Hlid | Hlid].
  - rewrite length_app. simpl.
    pose proof (removelast_length_nonempty
                  Segment (reconnect_segs l sub r h l)) as Hlen.
    assert (Hmap : reconnect_segs l sub r h l <> []).
    { intros Hnil. apply (proj1 Hlid).
      apply length_zero_iff_nil.
      pose proof (f_equal (@length Segment) Hnil) as Hlen0.
      rewrite reconnect_segs_length in Hlen0. exact Hlen0. }
    specialize (Hlen Hmap). rewrite reconnect_segs_length in Hlen. lia.
  - apply reconnect_segs_length.
Qed.

Lemma reconnect_right_length : forall l sub r h,
  length (reconnect_right l sub r h) = length r.
Proof.
  intros l sub r h. unfold reconnect_right.
  destruct (excluded_middle_informative (initial_lid r)) as [Hlid | Hlid].
  - destruct r as [|s r].
    + exfalso. apply (proj1 Hlid). reflexivity.
    + simpl. rewrite reconnect_segs_length. reflexivity.
  - apply reconnect_segs_length.
Qed.

Lemma reconnect_split_safe_length : forall l sub r h,
  length (reconnect_split l sub r h) = length (l ++ sub ++ r).
Proof.
  intros. unfold reconnect_split. repeat rewrite length_app.
  rewrite reconnect_left_length, reconnect_right_length. reflexivity.
Qed.

Definition same_segment_box (s t : Segment) : Prop :=
  init s = init t /\ term s = term t.

Lemma same_segment_box_rect : forall s t,
  same_segment_box s t -> rect_of [s] = rect_of [t].
Proof.
  intros s t [Hinit Hterm].
  change
    (mkRect
       (Rmin (fst (init s)) (fst (term s)))
       (Rmin (snd (init s)) (snd (term s)))
       (Rmax (fst (init s)) (fst (term s)))
       (Rmax (snd (init s)) (snd (term s))) =
     mkRect
       (Rmin (fst (init t)) (fst (term t)))
       (Rmin (snd (init t)) (snd (term t)))
       (Rmax (fst (init t)) (fst (term t)))
       (Rmax (snd (init t)) (snd (term t)))).
  now rewrite Hinit, Hterm.
Qed.

Lemma same_segment_box_contains : forall s t p,
  same_segment_box s t ->
  in_segment_rect_or_endpoints s p ->
  in_segment_rect_or_endpoints t p.
Proof.
  intros s t p Hbox Hp.
  unfold in_segment_rect_or_endpoints in *.
  now rewrite <- (same_segment_box_rect s t Hbox).
Qed.

(* sub に隣接する二つの蓋は [nonadjacent_sides] から除かれるので、
   sub 周りで検査する安全版の列は通常再接続版と完全に一致する。 *)
Lemma safe_nonadjacent_sides_eq_ordinary : forall l sub r h,
  nonadjacent_sides
    (reconnect_left l sub r h)
    (reconnect_right l sub r h)
  =
  nonadjacent_sides
    (reconnect_segs l sub r h l)
    (reconnect_segs l sub r h r).
Proof.
  intros l sub r h.
  unfold nonadjacent_sides, reconnect_left, reconnect_right.
  destruct (excluded_middle_informative (terminal_lid l)) as [Hleft | Hleft];
  destruct (excluded_middle_informative (initial_lid r)) as [Hright | Hright].
  - rewrite removelast_last.
    destruct r as [|s r].
    + exfalso. apply (proj1 Hright). reflexivity.
    + simpl. reflexivity.
  - rewrite removelast_last. reflexivity.
  - destruct r as [|s r].
    + exfalso. apply (proj1 Hright). reflexivity.
    + simpl. reflexivity.
  - reflexivity.
Qed.

(* 安全版で変更し得る左蓋が列の先頭でもあるのは [l] が singleton の
   場合だけであり、その場合も始点と始点傾きが通常版と一致する。 *)
Lemma safe_head_extension_iff_ordinary :
  forall ds l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    onHead_extend (reconnect_split l sub r h) p <->
    onHead_extend (ordinary_reconnect_split l sub r h) p.
Proof.
  intros ds l sub r h p Hne Hconn Hmono Hh Hsparse Hembed Hext.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { now apply (embed_listDir_connected ds (l ++ sub ++ r)). }
  destruct l as [|a [|b l']].
  - destruct sub as [|s sub']; [contradiction |].
    unfold reconnect_split, ordinary_reconnect_split, reconnect_left,
      reconnect_right, reconnect_segs, onHead_extend, hd_segment.
    destruct (excluded_middle_informative (terminal_lid [])) as [Hlid | Hlid].
    + exfalso. apply (proj1 Hlid). reflexivity.
    + simpl. reflexivity.
  - unfold reconnect_split, ordinary_reconnect_split, reconnect_left,
      reconnect_segs, onHead_extend, hd_segment.
    destruct (excluded_middle_informative (terminal_lid [a])) as [Hlid | Hlid].
    2: simpl; reflexivity.
    simpl.
    pose proof (choose_terminal_lid_spec
                  [a] sub r h Hne Hconn Hmono Hh Hsparse Hwhole
                  (ex_intro _ ds Hembed) Hext Hlid) as Hchosen.
    unfold terminal_lid_reconnect_spec in Hchosen.
    destruct Hchosen as [HchosenRec [HchosenSlope _]].
    assert (HaIn : In a ([a] ++ sub ++ r)) by (simpl; auto).
    assert (HaRec : reconnectable_after [a] sub r h a).
    { eapply operate_one_endpoints_reconnectable; eauto. }
    assert (Hinit :
      init (choose_terminal_lid [a] sub r h) =
      init (reconnect_one [a] sub r h a)).
    { unfold reconnects_after in HchosenRec.
      rewrite (proj1 HchosenRec).
      symmetry. now apply reconnect_one_init. }
    assert (Hslope :
      slope_init (choose_terminal_lid [a] sub r h) =
      slope_init (reconnect_one [a] sub r h a)).
    { rewrite HchosenSlope.
      symmetry. eapply reconnect_one_head_slope_init.
      + discriminate.
      + reflexivity.
      + exact (reconnect_head_init_slope_after
                 ds [a] sub r h Hne Hconn Hmono Hsparse Hembed Hext
                 (Rlt_le _ _ (proj1 Hh)) ltac:(discriminate)). }
    exact (head_extension_determined_by_init_slope
             (choose_terminal_lid [a] sub r h)
             (reconnect_one [a] sub r h a) Hinit Hslope p).
  - unfold reconnect_split, ordinary_reconnect_split, reconnect_left,
      reconnect_segs, onHead_extend, hd_segment.
    destruct (excluded_middle_informative (terminal_lid (a :: b :: l')));
      simpl; reflexivity.
Qed.

(* 右側についての双対。安全な右蓋が列の末尾でもある singleton の
   場合には、終点と終点傾きの保存から延長線の一致を得る。 *)
Lemma safe_last_extension_iff_ordinary :
  forall ds l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    onLast_extend (reconnect_split l sub r h) p <->
    onLast_extend (ordinary_reconnect_split l sub r h) p.
Proof.
  intros ds l sub r h p Hne Hconn Hmono Hh Hsparse Hembed Hext.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { now apply (embed_listDir_connected ds (l ++ sub ++ r)). }
  destruct r as [|a [|b r']].
  - assert (HsafeLast :
        last_segment (reconnect_split l sub [] h) = last_segment sub).
    { unfold reconnect_split, reconnect_right.
      destruct (excluded_middle_informative (initial_lid [])) as [Hlid | Hlid].
      - exfalso. apply (proj1 Hlid). reflexivity.
      - simpl. rewrite app_nil_r. now apply last_app_nonnil. }
    assert (HordinaryLast :
        last_segment (ordinary_reconnect_split l sub [] h) = last_segment sub).
    { unfold ordinary_reconnect_split, reconnect_segs. simpl.
      rewrite app_nil_r. now apply last_app_nonnil. }
    unfold onLast_extend. now rewrite HsafeLast, HordinaryLast.
  - unfold onLast_extend.
    destruct (excluded_middle_informative (initial_lid [a])) as [Hlid | Hlid].
    2: {
      assert (HsafeLast :
          last_segment (reconnect_split l sub [a] h) =
          reconnect_one l sub [a] h a).
      { unfold reconnect_split.
        rewrite (last_app_nonnil (reconnect_left l sub [a] h)
                   (sub ++ reconnect_right l sub [a] h)) by
          (destruct sub; [contradiction | discriminate]).
        rewrite (last_app_nonnil sub (reconnect_right l sub [a] h)).
        - unfold reconnect_right, reconnect_segs.
          destruct (excluded_middle_informative (initial_lid [a]));
            [contradiction | reflexivity].
        - unfold reconnect_right.
          destruct (excluded_middle_informative (initial_lid [a]));
            [contradiction | discriminate]. }
      assert (HordinaryLast :
          last_segment (ordinary_reconnect_split l sub [a] h) =
          reconnect_one l sub [a] h a).
      { unfold ordinary_reconnect_split, reconnect_segs.
        transitivity
          (last_segment (sub ++ [reconnect_one l sub [a] h a])).
        - apply last_app_nonnil. destruct sub; [contradiction | discriminate].
        - transitivity (last_segment [reconnect_one l sub [a] h a]).
          + apply last_app_nonnil. discriminate.
          + reflexivity. }
      now rewrite HsafeLast, HordinaryLast. }
    assert (HsafeLast :
        last_segment (reconnect_split l sub [a] h) =
        choose_initial_lid l sub [a] h).
    { unfold reconnect_split.
      rewrite (last_app_nonnil (reconnect_left l sub [a] h)
                 (sub ++ reconnect_right l sub [a] h)) by
        (destruct sub; [contradiction | discriminate]).
      rewrite (last_app_nonnil sub (reconnect_right l sub [a] h)).
      - unfold reconnect_right.
        destruct (excluded_middle_informative (initial_lid [a]));
          [reflexivity | contradiction].
      - unfold reconnect_right.
        destruct (excluded_middle_informative (initial_lid [a]));
          [discriminate | contradiction]. }
    assert (HordinaryLast :
        last_segment (ordinary_reconnect_split l sub [a] h) =
        reconnect_one l sub [a] h a).
    { unfold ordinary_reconnect_split, reconnect_segs.
      transitivity
        (last_segment (sub ++ [reconnect_one l sub [a] h a])).
      - apply last_app_nonnil. destruct sub; [contradiction | discriminate].
      - transitivity (last_segment [reconnect_one l sub [a] h a]).
        + apply last_app_nonnil. destruct sub; discriminate.
        + reflexivity. }
    rewrite HsafeLast, HordinaryLast.
    pose proof (choose_initial_lid_spec
                  l sub [a] h Hne Hconn Hmono Hh Hsparse Hwhole
                  (ex_intro _ ds Hembed) Hext Hlid) as Hchosen.
    unfold initial_lid_reconnect_spec in Hchosen.
    destruct Hchosen as [HchosenRec [HchosenSlope _]].
    assert (HaIn : In a (l ++ sub ++ [a])).
    { apply in_or_app. right. apply in_or_app. right. now left. }
    assert (HaRec : reconnectable_after l sub [a] h a).
    { eapply operate_one_endpoints_reconnectable; eauto. }
    assert (Hterm :
      term (choose_initial_lid l sub [a] h) =
      term (reconnect_one l sub [a] h a)).
    { unfold reconnects_after in HchosenRec.
      rewrite (proj1 (proj2 HchosenRec)).
      symmetry. now apply reconnect_one_term. }
    assert (HnotHead : ~ head_init_slope_after l sub [a] h a).
    { unfold head_init_slope_after. intros [Hl [Heq _]].
      eapply (sparse_head_last_distinct_across_sub l sub [a]); eauto.
      now symmetry. }
    assert (Hslope :
      slope_term (choose_initial_lid l sub [a] h) =
      slope_term (reconnect_one l sub [a] h a)).
    { rewrite HchosenSlope.
      symmetry. eapply reconnect_one_last_slope_term.
      + exact HnotHead.
      + discriminate.
      + reflexivity.
      + exact (reconnect_last_term_slope_after
                 ds l sub [a] h Hne Hconn Hmono Hsparse Hembed Hext
                 (Rlt_le _ _ (proj1 Hh)) ltac:(discriminate)). }
    exact (last_extension_determined_by_term_slope
             (choose_initial_lid l sub [a] h)
             (reconnect_one l sub [a] h a) Hterm Hslope p).
  - unfold onLast_extend.
    set (f := reconnect_one l sub (a :: b :: r') h).
    assert (Htail : map f (b :: r') <> []) by discriminate.
    assert (HsafeLast :
        last_segment (reconnect_split l sub (a :: b :: r') h) =
        last_segment (map f (b :: r'))).
    { unfold reconnect_split, reconnect_right, reconnect_segs.
      destruct (excluded_middle_informative (initial_lid (a :: b :: r'))).
      - change
          (last_segment
             (reconnect_left l sub (a :: b :: r') h ++ sub ++
              choose_initial_lid l sub (a :: b :: r') h :: map f (b :: r')) =
           last_segment (map f (b :: r'))).
        transitivity
          (last_segment
             (sub ++ choose_initial_lid l sub (a :: b :: r') h ::
              map f (b :: r'))).
        + apply last_app_nonnil. destruct sub; discriminate.
        + transitivity
            (last_segment
               (choose_initial_lid l sub (a :: b :: r') h ::
                map f (b :: r'))).
          * apply last_app_nonnil. discriminate.
          * change
              (last_segment
                 ([choose_initial_lid l sub (a :: b :: r') h] ++
                  map f (b :: r')) =
               last_segment (map f (b :: r'))).
            apply last_app_nonnil. exact Htail.
      - change
          (last_segment
             (reconnect_left l sub (a :: b :: r') h ++ sub ++
              f a :: map f (b :: r')) =
           last_segment (map f (b :: r'))).
        transitivity (last_segment (sub ++ f a :: map f (b :: r'))).
        + apply last_app_nonnil. destruct sub; discriminate.
        + transitivity (last_segment (f a :: map f (b :: r'))).
          * apply last_app_nonnil. discriminate.
          * change
              (last_segment ([f a] ++ map f (b :: r')) =
               last_segment (map f (b :: r'))).
            apply last_app_nonnil. exact Htail. }
    assert (HordinaryLast :
        last_segment (ordinary_reconnect_split l sub (a :: b :: r') h) =
        last_segment (map f (b :: r'))).
    { unfold ordinary_reconnect_split, reconnect_segs.
      change
        (last_segment
           (map f l ++ sub ++ f a :: map f (b :: r')) =
         last_segment (map f (b :: r'))).
      transitivity (last_segment (sub ++ f a :: map f (b :: r'))).
      - apply last_app_nonnil. destruct sub; discriminate.
      - transitivity (last_segment (f a :: map f (b :: r'))).
        + apply last_app_nonnil. discriminate.
        + change
            (last_segment ([f a] ++ map f (b :: r')) =
             last_segment (map f (b :: r'))).
          apply last_app_nonnil. exact Htail. }
    now rewrite HsafeLast, HordinaryLast.
Qed.

(* 安全な蓋への置換後も、各位置の端点と向きは通常再接続と同じである。 *)
Lemma reconnect_left_reconnects_after :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    reconnects_list_after l sub r h l (reconnect_left l sub r h).
Proof.
  intros l sub r h Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hrec.
  unfold reconnect_left.
  destruct (excluded_middle_informative (terminal_lid l)) as [Hlid | Hlid].
  - destruct (exists_last (proj1 Hlid)) as [l0 [x Heq]].
    subst l.
    unfold reconnect_segs. rewrite map_app. simpl. rewrite removelast_last.
    apply Forall2_app.
    + apply reconnect_segs_reconnects_after.
      intros s Hs. apply Hrec. rewrite !in_app_iff. auto.
    + constructor; [|constructor].
      change (reconnects_after (l0 ++ [x]) sub r h x
        (choose_terminal_lid (l0 ++ [x]) sub r h)).
      pose proof (choose_terminal_lid_spec
                    (l0 ++ [x]) sub r h Hne Hconn Hmono Hh Hsparse
                    Hwhole Hembedded Hext Hlid) as Hchosen.
      rewrite (last_app_nonnil l0 [x]) in Hchosen by discriminate.
      simpl in Hchosen.
      exact (proj1 Hchosen).
  - apply reconnect_segs_reconnects_after.
    intros s Hs. apply Hrec. rewrite !in_app_iff. auto.
Qed.

Lemma reconnect_right_reconnects_after :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    reconnects_list_after l sub r h r (reconnect_right l sub r h).
Proof.
  intros l sub r h Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hrec.
  unfold reconnect_right.
  destruct (excluded_middle_informative (initial_lid r)) as [Hlid | Hlid].
  - destruct r as [|x r].
    + exfalso. apply (proj1 Hlid). reflexivity.
    + simpl. constructor.
      * change (reconnects_after l sub (x :: r) h x
          (choose_initial_lid l sub (x :: r) h)).
        pose proof (choose_initial_lid_spec
                      l sub (x :: r) h Hne Hconn Hmono Hh Hsparse
                      Hwhole Hembedded Hext Hlid) as Hchosen.
        exact (proj1 Hchosen).
      * change (reconnects_list_after l sub (x :: r) h r
          (reconnect_segs l sub (x :: r) h r)).
        apply reconnect_segs_reconnects_after.
        eapply all_reconnectable_mono; [exact Hrec |].
        intros s0 Hs0. rewrite !in_app_iff. simpl. tauto.
  - apply reconnect_segs_reconnects_after.
    intros s Hs. apply Hrec. rewrite !in_app_iff. auto.
Qed.

Lemma Forall2_nth_error_relation :
  forall (A B : Type) (R : A -> B -> Prop) xs ys,
    Forall2 R xs ys ->
    forall i,
      match nth_error xs i, nth_error ys i with
      | Some x, Some y => R x y
      | None, None => True
      | _, _ => False
      end.
Proof.
  intros A B R xs ys Hrel. induction Hrel.
  - intros [|i]; simpl; exact I.
  - intros [|i]; simpl; [exact H | now apply IHHrel].
Qed.

(* 各位置で移動後の端点と向きを共有する列は、元と同じ向き列を埋め込む。 *)
Lemma reconnects_list_preserves_embed :
  forall l sub r h old new ds,
    reconnects_list_after l sub r h old new ->
    embed_listDir ds old ->
    embed_listDir ds new.
Proof.
  intros l sub r h old new ds Hrel Hembed.
  eapply embed_scurve_transfer; [exact Hembed | | |].
  - symmetry. now apply Forall2_length in Hrel.
  - intros i s s' Hold Hnew.
    pose proof (Forall2_nth_error_relation
                  Segment Segment (reconnects_after l sub r h)
                  old new Hrel i) as Hi.
    rewrite Hold, Hnew in Hi. exact (proj2 (proj2 Hi)).
  - intros i s1 s2 Hnew1 Hnew2.
    pose proof (Forall2_length Hrel) as Hlen.
    assert (Hi : (i < length old)%nat).
    { rewrite Hlen. now apply nth_error_lt in Hnew1. }
    assert (HSi : (S i < length old)%nat).
    { rewrite Hlen. now apply nth_error_lt in Hnew2. }
    destruct (nth_error old i) as [old1 |] eqn:Hold1.
    2: exfalso; apply (proj2 (nth_error_Some old i) Hi); exact Hold1.
    destruct (nth_error old (S i)) as [old2 |] eqn:Hold2.
    2: exfalso; apply (proj2 (nth_error_Some old (S i)) HSi); exact Hold2.
    pose proof (Forall2_nth_error_relation
                  Segment Segment (reconnects_after l sub r h)
                  old new Hrel i) as Hspec1.
    pose proof (Forall2_nth_error_relation
                  Segment Segment (reconnects_after l sub r h)
                  old new Hrel (S i)) as Hspec2.
    rewrite Hold1, Hnew1 in Hspec1.
    rewrite Hold2, Hnew2 in Hspec2.
    unfold reconnects_after in Hspec1, Hspec2.
    rewrite (proj1 (proj2 Hspec1)), (proj1 Hspec2).
    f_equal. exact (embed_listDir_connected ds old Hembed i old1 old2 Hold1 Hold2).
Qed.

(* 左右の安全な蓋と固定した sub を合わせても、全位置で再接続仕様を満たす。 *)
Lemma reconnect_split_reconnects_after :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    reconnects_list_after l sub r h (l ++ sub ++ r)
      (reconnect_split l sub r h).
Proof.
  intros l sub r h Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hrec.
  unfold reconnect_split.
  apply Forall2_app.
  - eapply reconnect_left_reconnects_after; eauto.
  - apply Forall2_app.
    + assert (Hsub : forall xs,
          (forall s, In s xs -> In s sub) ->
          reconnects_list_after l sub r h xs xs).
      { intros xs Hin. induction xs as [|s xs IH]; constructor.
        - unfold reconnects_after. repeat split; try reflexivity.
          + symmetry. apply operate_sub_endpoint.
            exists s. split; [apply Hin; now left | now left].
          + symmetry. apply operate_sub_endpoint.
            exists s. split; [apply Hin; now left | now right].
        - apply IH. intros t Ht. apply Hin. now right. }
      apply Hsub. auto.
    + eapply reconnect_right_reconnects_after; eauto.
Qed.

Lemma reconnect_split_safe_preserves_embed :
  forall l sub r h ds,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    embed_listDir ds (reconnect_split l sub r h).
Proof.
  intros l sub r h ds Hne Hconn Hmono Hh Hsparse Hwhole Hext Hrec Hembed.
  eapply reconnects_list_preserves_embed; [|exact Hembed].
  eapply reconnect_split_reconnects_after; eauto.
Qed.

(* split の同じ位置にある新旧セグメントは向きと operate 後の端点を共有する。 *)
Lemma ordinary_reconnect_split_nth_spec :
  forall l sub r h i s s',
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (ordinary_reconnect_split l sub r h) i = Some s' ->
    orn_seg s' = orn_seg s
    /\ init s' = operate_point l sub r h (init s)
    /\ term s' = operate_point l sub r h (term s).
Proof.
  intros l sub r h i s s' Hne Hconn Hmono Hsparse Hwhole Hembedded
    Hrec Hold Hnew.
  destruct (Nat.lt_ge_cases i (length l)) as [Hil | Hil].
  - assert (Holdl : nth_error l i = Some s).
    { rewrite <- (nth_error_app1 l (sub ++ r) Hil). exact Hold. }
    assert (Hlenl : length (reconnect_segs l sub r h l) = length l).
    { apply reconnect_segs_length. }
    assert (Hnewl :
        nth_error (reconnect_segs l sub r h l) i = Some s').
    { rewrite <- Hnew. unfold ordinary_reconnect_split.
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
    { pose proof Hnew as Hnew'. unfold ordinary_reconnect_split in Hnew'.
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
Lemma ordinary_reconnect_split_preserves_embed :
  forall l sub r h ds,
    sub <> [] ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    embed_listDir ds (ordinary_reconnect_split l sub r h).
Proof.
  intros l sub r h ds Hne Hmono Hsparse Hrec Hembed.
  assert (Hconn : connected sub).
  { apply connected_middle with (l := l) (r := r).
    now apply embed_listDir_connected with (ds := ds). }
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  eapply embed_scurve_transfer; [exact Hembed | | |].
  - unfold ordinary_reconnect_split. repeat rewrite length_app.
    rewrite !reconnect_segs_length. reflexivity.
  - intros i s s' Hold Hnew.
    exact (proj1 (ordinary_reconnect_split_nth_spec
                    l sub r h i s s' Hne Hconn Hmono Hsparse Hwhole
                    (ex_intro _ ds Hembed) Hrec Hold Hnew)).
  - intros i s1 s2 H1 H2.
    assert (Hlen :
        length (ordinary_reconnect_split l sub r h) = length (l ++ sub ++ r)).
    { unfold ordinary_reconnect_split. repeat rewrite length_app.
      rewrite !reconnect_segs_length. reflexivity. }
    assert (Hi : (i < length (l ++ sub ++ r))%nat).
    { rewrite <- Hlen. now apply nth_error_lt in H1. }
    assert (HSi : (S i < length (l ++ sub ++ r))%nat).
    { rewrite <- Hlen. now apply nth_error_lt in H2. }
    destruct (nth_error (l ++ sub ++ r) i) as [old1 |] eqn:E1.
    2: exfalso; apply (proj2 (nth_error_Some _ _) Hi); exact E1.
    destruct (nth_error (l ++ sub ++ r) (S i)) as [old2 |] eqn:E2.
    2: exfalso; apply (proj2 (nth_error_Some _ _) HSi); exact E2.
    pose proof (ordinary_reconnect_split_nth_spec
                  l sub r h i old1 s1 Hne Hconn Hmono Hsparse Hwhole
                  (ex_intro _ ds Hembed) Hrec E1 H1)
      as [_ [_ Hterm]].
    pose proof (ordinary_reconnect_split_nth_spec
                  l sub r h (S i) old2 s2 Hne Hconn Hmono Hsparse Hwhole
                  (ex_intro _ ds Hembed) Hrec E2 H2)
      as [_ [Hinit _]].
    rewrite Hterm, Hinit.
    f_equal. exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed
                      i old1 old2 E1 E2).
Qed.

Lemma ordinary_reconnect_split_length : forall l sub r h,
  length (ordinary_reconnect_split l sub r h) = length (l ++ sub ++ r).
Proof.
  intros. unfold ordinary_reconnect_split. repeat rewrite length_app.
  rewrite !reconnect_segs_length. reflexivity.
Qed.

(* 同じ旧セグメントに対応する通常版と安全版は、曲線の選び方が違っても
   二端点と向きが一致する。蓋の blocker を安全版へ輸送する基本補題。 *)
Lemma ordinary_safe_nth_same_box :
  forall l sub r h i old ordinary safe,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    nth_error (l ++ sub ++ r) i = Some old ->
    nth_error (ordinary_reconnect_split l sub r h) i = Some ordinary ->
    nth_error (reconnect_split l sub r h) i = Some safe ->
    same_segment_box ordinary safe /\ orn_seg ordinary = orn_seg safe.
Proof.
  intros l sub r h i old ordinary safe Hne Hconn Hmono Hh Hsparse Hwhole
    Hembedded Hext Hrec Hold Hordinary Hsafe.
  pose proof (ordinary_reconnect_split_nth_spec
                l sub r h i old ordinary Hne Hconn Hmono Hsparse Hwhole
                Hembedded Hrec Hold Hordinary) as HordinarySpec.
  pose proof (reconnect_split_reconnects_after
                l sub r h Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext
                Hrec) as HsafeRel.
  pose proof (Forall2_nth_error_relation
                Segment Segment (reconnects_after l sub r h)
                (l ++ sub ++ r) (reconnect_split l sub r h)
                HsafeRel i) as HsafeSpec.
  rewrite Hold, Hsafe in HsafeSpec.
  unfold reconnects_after in HsafeSpec.
  destruct HordinarySpec as [HordinaryOrn [HordinaryInit HordinaryTerm]].
  destruct HsafeSpec as [HsafeInit [HsafeTerm HsafeOrn]].
  split.
  - unfold same_segment_box. split; congruence.
  - congruence.
Qed.

Lemma nth_error_zero_hd_segment : forall ls,
  ls <> [] -> nth_error ls 0 = Some (hd_segment ls).
Proof.
  intros [|s ls] Hne; [contradiction | reflexivity].
Qed.

Lemma ordinary_safe_head_same_box :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    same_segment_box
      (hd_segment (ordinary_reconnect_split l sub r h))
      (hd_segment (reconnect_split l sub r h)).
Proof.
  intros l sub r h Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hrec.
  assert (HoldNe : l ++ sub ++ r <> []).
  { intros Hnil. apply app_eq_nil in Hnil as [_ Htail].
    apply app_eq_nil in Htail as [Hsub _]. contradiction. }
  assert (HordinaryNe : ordinary_reconnect_split l sub r h <> []).
  { intros Hnil. apply HoldNe, length_zero_iff_nil.
    rewrite <- (ordinary_reconnect_split_length l sub r h). now rewrite Hnil. }
  assert (HsafeNe : reconnect_split l sub r h <> []).
  { intros Hnil. apply HoldNe, length_zero_iff_nil.
    rewrite <- (reconnect_split_safe_length l sub r h). now rewrite Hnil. }
  pose proof (ordinary_safe_nth_same_box
                l sub r h 0
                (hd_segment (l ++ sub ++ r))
                (hd_segment (ordinary_reconnect_split l sub r h))
                (hd_segment (reconnect_split l sub r h))
                Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hrec
                (nth_error_zero_hd_segment _ HoldNe)
                (nth_error_zero_hd_segment _ HordinaryNe)
                (nth_error_zero_hd_segment _ HsafeNe)) as [Hbox _].
  exact Hbox.
Qed.

Lemma ordinary_safe_last_same_box :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    same_segment_box
      (last_segment (ordinary_reconnect_split l sub r h))
      (last_segment (reconnect_split l sub r h)).
Proof.
  intros l sub r h Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hrec.
  set (old := l ++ sub ++ r).
  set (ordinary := ordinary_reconnect_split l sub r h).
  set (safe := reconnect_split l sub r h).
  assert (HoldNe : old <> []).
  { unfold old. intros Hnil. apply app_eq_nil in Hnil as [_ Htail].
    apply app_eq_nil in Htail as [Hsub _]. contradiction. }
  assert (HordinaryLen : length ordinary = length old).
  { unfold ordinary, old. apply ordinary_reconnect_split_length. }
  assert (HsafeLen : length safe = length old).
  { unfold safe, old. apply reconnect_split_safe_length. }
  assert (HordinaryNe : ordinary <> []).
  { intros Hnil. apply HoldNe, length_zero_iff_nil.
    rewrite <- HordinaryLen. now rewrite Hnil. }
  assert (HsafeNe : safe <> []).
  { intros Hnil. apply HoldNe, length_zero_iff_nil.
    rewrite <- HsafeLen. now rewrite Hnil. }
  assert (HoldNth :
      nth_error old (length old - 1) = Some (last_segment old)).
  { exact (@nth_error_last Segment old default_segment HoldNe). }
  assert (HordinaryNth :
      nth_error ordinary (length old - 1) = Some (last_segment ordinary)).
  { rewrite <- HordinaryLen.
    exact (@nth_error_last Segment ordinary default_segment HordinaryNe). }
  assert (HsafeNth :
      nth_error safe (length old - 1) = Some (last_segment safe)).
  { rewrite <- HsafeLen.
    exact (@nth_error_last Segment safe default_segment HsafeNe). }
  unfold old, ordinary, safe in *.
  pose proof (ordinary_safe_nth_same_box
                l sub r h (length (l ++ sub ++ r) - 1)
                (last_segment (l ++ sub ++ r))
                (last_segment (ordinary_reconnect_split l sub r h))
                (last_segment (reconnect_split l sub r h))
                Hne Hconn Hmono Hh Hsparse Hwhole Hembedded Hext Hrec
                HoldNth HordinaryNth HsafeNth) as [Hbox _].
  exact Hbox.
Qed.

Lemma strict_head_extension_same : forall s t p,
  init s = init t ->
  (forall q, onHead s q <-> onHead t q) ->
  (exists u, u < 0 /\ point s u = p) <->
  (exists u, u < 0 /\ point t u = p).
Proof.
  intros s t p Hinit Hext. split; intros [u [Hu Hp]].
  - assert (Hon : onHead s p).
    { exists u. split; [lra | exact Hp]. }
    destruct (proj1 (Hext p) Hon) as [v [Hv Hvp]].
    exists v. split; [|exact Hvp].
    destruct (Req_dec v 0) as [-> | Hneq]; [|lra].
    exfalso. apply (Rlt_irrefl 0).
    assert (Hu0 : u = 0).
    { apply (point_injective s).
      rewrite Hp, <- Hvp. change (init t = init s). now symmetry. }
    now rewrite Hu0 in Hu.
  - assert (Hon : onHead t p).
    { exists u. split; [lra | exact Hp]. }
    destruct (proj2 (Hext p) Hon) as [v [Hv Hvp]].
    exists v. split; [|exact Hvp].
    destruct (Req_dec v 0) as [-> | Hneq]; [|lra].
    exfalso. apply (Rlt_irrefl 0).
    assert (Hu0 : u = 0).
    { apply (point_injective t).
      rewrite Hp, <- Hvp. change (init s = init t). exact Hinit. }
    now rewrite Hu0 in Hu.
Qed.

Lemma strict_last_extension_same : forall s t p,
  term s = term t ->
  (forall q, onLast s q <-> onLast t q) ->
  (exists u, 1 < u /\ point s u = p) <->
  (exists u, 1 < u /\ point t u = p).
Proof.
  intros s t p Hterm Hext. split; intros [u [Hu Hp]].
  - assert (Hon : onLast s p).
    { exists u. split; [lra | exact Hp]. }
    destruct (proj1 (Hext p) Hon) as [v [Hv Hvp]].
    exists v. split; [|exact Hvp].
    destruct (Req_dec v 1) as [-> | Hneq]; [|lra].
    exfalso. apply (Rlt_irrefl 1).
    assert (Hu1 : u = 1).
    { apply (point_injective s).
      rewrite Hp, <- Hvp. change (term t = term s). now symmetry. }
    now rewrite Hu1 in Hu.
  - assert (Hon : onLast t p).
    { exists u. split; [lra | exact Hp]. }
    destruct (proj2 (Hext p) Hon) as [v [Hv Hvp]].
    exists v. split; [|exact Hvp].
    destruct (Req_dec v 1) as [-> | Hneq]; [|lra].
    exfalso. apply (Rlt_irrefl 1).
    assert (Hu1 : u = 1).
    { apply (point_injective t).
      rewrite Hp, <- Hvp. change (term s = term t). exact Hterm. }
    now rewrite Hu1 in Hu.
Qed.

Lemma safe_head_strict_extension_iff_ordinary :
  forall ds l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    onHead_extend_strict (reconnect_split l sub r h) p <->
    onHead_extend_strict (ordinary_reconnect_split l sub r h) p.
Proof.
  intros ds l sub r h p Hne Hconn Hmono Hh Hsparse Hembed Hext.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { now apply (embed_listDir_connected ds (l ++ sub ++ r)). }
  pose proof (operate_endpoints_reconnectable
                l sub r h Hne Hconn Hmono Hh Hsparse Hwhole
                (ex_intro _ ds Hembed) Hext) as Hrec.
  pose proof (ordinary_safe_head_same_box
                l sub r h Hne Hconn Hmono Hh Hsparse Hwhole
                (ex_intro _ ds Hembed) Hext Hrec) as Hbox.
  unfold onHead_extend_strict.
  eapply strict_head_extension_same.
  - symmetry. exact (proj1 Hbox).
  - intros q. exact (safe_head_extension_iff_ordinary
                       ds l sub r h q Hne Hconn Hmono Hh Hsparse Hembed Hext).
Qed.

Lemma safe_last_strict_extension_iff_ordinary :
  forall ds l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    onLast_extend_strict (reconnect_split l sub r h) p <->
    onLast_extend_strict (ordinary_reconnect_split l sub r h) p.
Proof.
  intros ds l sub r h p Hne Hconn Hmono Hh Hsparse Hembed Hext.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { now apply (embed_listDir_connected ds (l ++ sub ++ r)). }
  pose proof (operate_endpoints_reconnectable
                l sub r h Hne Hconn Hmono Hh Hsparse Hwhole
                (ex_intro _ ds Hembed) Hext) as Hrec.
  pose proof (ordinary_safe_last_same_box
                l sub r h Hne Hconn Hmono Hh Hsparse Hwhole
                (ex_intro _ ds Hembed) Hext Hrec) as Hbox.
  unfold onLast_extend_strict.
  eapply strict_last_extension_same.
  - symmetry. exact (proj2 Hbox).
  - intros q. exact (safe_last_extension_iff_ordinary
                       ds l sub r h q Hne Hconn Hmono Hh Hsparse Hembed Hext).
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

(* [reconnect_split] で通常再接続から実際に置換され得る二つの位置。
   左の末尾蓋と右の先頭蓋以外では、安全版と通常版は同じ曲線である。 *)
Definition reconnect_split_lid_index
    (l sub r : list Segment) (i : nat) : Prop :=
  (terminal_lid l /\ i = (length l - 1)%nat)
  \/ (initial_lid r /\ i = (length l + length sub)%nat).

(* 安全版の出現から、同じ添字にある元セグメントと通常再接続版を取る。
   ここでは長さ保存しか使わず、曲線の幾何には触れない。 *)
Lemma reconnect_split_nth_witnesses :
  forall l sub r h i safe,
    nth_error (reconnect_split l sub r h) i = Some safe ->
    exists old ordinary,
      nth_error (l ++ sub ++ r) i = Some old
      /\ nth_error (ordinary_reconnect_split l sub r h) i = Some ordinary.
Proof.
  intros l sub r h i safe Hsafe.
  destruct (nth_error_exists_at_equal_length
              (l ++ sub ++ r) (reconnect_split l sub r h) i safe)
    as [old Hold].
  { symmetry. apply reconnect_split_safe_length. }
  { exact Hsafe. }
  destruct (nth_error_exists_at_equal_length
              (ordinary_reconnect_split l sub r h)
              (reconnect_split l sub r h) i safe)
    as [ordinary Hordinary].
  { rewrite ordinary_reconnect_split_length,
      reconnect_split_safe_length. reflexivity. }
  { exact Hsafe. }
  now exists old, ordinary.
Qed.

(* 蓋位置でなければ、[reconnect_split] は通常再接続の要素をそのまま使う。
   これは [reconnect_left]/[reconnect_right] のリスト操作だけから従う。 *)
Lemma nth_error_removelast_before_last :
  forall (A : Type) (xs : list A) i,
    (S i < length xs)%nat ->
    nth_error (removelast xs) i = nth_error xs i.
Proof.
  intros A xs. induction xs as [|a xs IH]; intros i Hi; [simpl in Hi; lia |].
  destruct xs as [|b xs].
  - simpl in Hi. lia.
  - destruct i as [|i].
    + reflexivity.
    + simpl. apply IH. simpl. now apply Nat.succ_lt_mono in Hi.
Qed.

Lemma reconnect_split_nth_eq_ordinary_unless_lid :
  forall l sub r h i ordinary safe,
    ~ reconnect_split_lid_index l sub r i ->
    nth_error (ordinary_reconnect_split l sub r h) i = Some ordinary ->
    nth_error (reconnect_split l sub r h) i = Some safe ->
    safe = ordinary.
Proof.
  intros l sub r h i ordinary safe HnotLid Hordinary Hsafe.
  destruct (Nat.lt_ge_cases i (length l)) as [Hil | Hil].
  - assert (HordinaryL :
        nth_error (reconnect_segs l sub r h l) i = Some ordinary).
    { rewrite <- Hordinary. unfold ordinary_reconnect_split.
      symmetry. apply nth_error_app1.
      now rewrite reconnect_segs_length. }
    assert (HsafeL : nth_error (reconnect_left l sub r h) i = Some safe).
    { rewrite <- Hsafe. unfold reconnect_split.
      symmetry. apply nth_error_app1.
      now rewrite reconnect_left_length. }
    unfold reconnect_left in HsafeL.
    destruct (excluded_middle_informative (terminal_lid l))
      as [Hterminal | Hterminal].
    + assert (Hinot : i <> (length l - 1)%nat).
      { intro Hi. apply HnotLid. left. now split. }
      assert (Hbefore : (S i < length l)%nat) by lia.
      assert (HremoveLen :
          length (removelast (reconnect_segs l sub r h l)) =
            (length l - 1)%nat).
      { pose proof (removelast_length_nonempty
                      Segment (reconnect_segs l sub r h l)) as Hlen.
        assert (Hmap : reconnect_segs l sub r h l <> []).
        { intro Hnil. apply (proj1 Hterminal).
          apply length_zero_iff_nil.
          pose proof (f_equal (@length Segment) Hnil) as Hzero.
          now rewrite reconnect_segs_length in Hzero. }
        specialize (Hlen Hmap). rewrite reconnect_segs_length in Hlen. lia. }
      rewrite nth_error_app1 in HsafeL by (rewrite HremoveLen; lia).
      rewrite (nth_error_removelast_before_last
                 Segment (reconnect_segs l sub r h l) i) in HsafeL
        by now rewrite reconnect_segs_length.
      congruence.
    + congruence.
  - set (k := (i - length l)%nat).
    assert (HordinaryTail :
        nth_error (sub ++ reconnect_segs l sub r h r) k = Some ordinary).
    { unfold k. unfold ordinary_reconnect_split in Hordinary.
      rewrite nth_error_app2 in Hordinary
        by (rewrite reconnect_segs_length; lia).
      now rewrite reconnect_segs_length in Hordinary. }
    assert (HsafeTail :
        nth_error (sub ++ reconnect_right l sub r h) k = Some safe).
    { unfold k. unfold reconnect_split in Hsafe.
      rewrite nth_error_app2 in Hsafe by (rewrite reconnect_left_length; lia).
      now rewrite reconnect_left_length in Hsafe. }
    destruct (Nat.lt_ge_cases k (length sub)) as [Hksub | Hksub].
    + rewrite nth_error_app1 in HordinaryTail by exact Hksub.
      rewrite nth_error_app1 in HsafeTail by exact Hksub.
      congruence.
    + set (q := (k - length sub)%nat).
      assert (HordinaryR :
          nth_error (reconnect_segs l sub r h r) q = Some ordinary).
      { unfold q. rewrite nth_error_app2 in HordinaryTail by lia.
        exact HordinaryTail. }
      assert (HsafeR : nth_error (reconnect_right l sub r h) q = Some safe).
      { unfold q. rewrite nth_error_app2 in HsafeTail by lia. exact HsafeTail. }
      unfold reconnect_right in HsafeR.
      destruct (excluded_middle_informative (initial_lid r))
        as [Hinitial | Hinitial].
      * assert (Hqnot : q <> 0%nat).
        { intro Hq. apply HnotLid. right. split; [exact Hinitial |].
          unfold q, k in Hq. lia. }
        destruct q as [|q]; [contradiction |].
        simpl in HsafeR.
        destruct r as [|a r']; [exfalso; apply (proj1 Hinitial); reflexivity |].
        simpl in HordinaryR, HsafeR. congruence.
      * congruence.
Qed.

(* 左蓋が有効なら、安全版の左部分の末尾添字には選択した蓋が現れる。 *)
Lemma reconnect_split_terminal_lid_nth :
  forall l sub r h,
    terminal_lid l ->
    nth_error (reconnect_split l sub r h) (length l - 1) =
      Some (choose_terminal_lid l sub r h).
Proof.
  intros l sub r h Hlid.
  destruct Hlid as [Hl Hwest].
  unfold reconnect_split.
  rewrite nth_error_app1.
  2: rewrite reconnect_left_length; destruct l; [contradiction | simpl; lia].
  unfold reconnect_left.
  destruct (excluded_middle_informative (terminal_lid l)) as [Hlid | Hlid].
  2: exfalso; apply Hlid; now split.
  assert (Hmap : reconnect_segs l sub r h l <> []).
  { intro Hnil. apply Hl. apply length_zero_iff_nil.
    pose proof (f_equal (@length Segment) Hnil) as Hlen.
    now rewrite reconnect_segs_length in Hlen. }
  assert (Hremove :
      length (removelast (reconnect_segs l sub r h l)) = (length l - 1)%nat).
  { pose proof (removelast_length_nonempty
                  Segment (reconnect_segs l sub r h l) Hmap) as Hlen.
    rewrite reconnect_segs_length in Hlen. lia. }
  rewrite nth_error_app2 by (rewrite Hremove; lia).
  rewrite Hremove. replace (length l - 1 - (length l - 1))%nat with 0%nat by lia.
  reflexivity.
Qed.

(* 左蓋から二つ以上離れた通常版の出現は、左蓋の blocker 列に入る。 *)
Lemma ordinary_far_from_terminal_lid_in_blockers :
  forall l sub r h j ordinary,
    terminal_lid l ->
    nth_error (ordinary_reconnect_split l sub r h) j = Some ordinary ->
    (S (length l - 1) < j \/ S j < length l - 1)%nat ->
    In ordinary (terminal_lid_blockers l sub r h).
Proof.
  intros l sub r h j ordinary [Hl Hwest] Hnth Hfar.
  assert (Hlpos : (0 < length l)%nat).
  { destruct l; [contradiction | simpl; lia]. }
  unfold ordinary_reconnect_split in Hnth.
  unfold terminal_lid_blockers, nonadjacent_sides.
  rewrite in_app_iff.
  destruct Hfar as [Hright | Hleft].
  - right.
    rewrite nth_error_app2 in Hnth
      by (rewrite reconnect_segs_length; lia).
    rewrite reconnect_segs_length in Hnth.
    set (k := (j - length l)%nat) in *.
    assert (Hk : (0 < k)%nat) by (unfold k; lia).
    destruct k as [|k]; [lia |].
    destruct (sub ++ reconnect_segs l sub r h r) as [|a tail] eqn:Htail.
    { simpl in Hnth. discriminate. }
    simpl in Hnth |- *.
    now apply nth_error_In in Hnth.
  - left.
    assert (HnthL :
        nth_error (reconnect_segs l sub r h l) j = Some ordinary).
    { rewrite nth_error_app1 in Hnth
        by (rewrite reconnect_segs_length; lia).
      exact Hnth. }
    assert (Hmap : reconnect_segs l sub r h l <> []).
    { intro Hnil. apply Hl. apply length_zero_iff_nil.
      pose proof (f_equal (@length Segment) Hnil) as Hzero.
      now rewrite reconnect_segs_length in Hzero. }
    assert (HremoveLen :
        length (removelast (reconnect_segs l sub r h l)) =
          (length l - 1)%nat).
    { pose proof (removelast_length_nonempty
                    Segment (reconnect_segs l sub r h l) Hmap) as Hlen.
      rewrite reconnect_segs_length in Hlen. lia. }
    assert (HnthRemove :
        nth_error (removelast (reconnect_segs l sub r h l)) j =
          Some ordinary).
    { rewrite nth_error_removelast_before_last.
      - exact HnthL.
      - rewrite reconnect_segs_length. lia. }
    apply nth_error_In with (n := j).
    rewrite nth_error_removelast_before_last.
    + exact HnthRemove.
    + now rewrite HremoveLen.
Qed.

(* 右蓋が有効なら、全体で [length l + length sub] の位置に現れる。 *)
Lemma reconnect_split_initial_lid_nth :
  forall l sub r h,
    initial_lid r ->
    nth_error (reconnect_split l sub r h) (length l + length sub) =
      Some (choose_initial_lid l sub r h).
Proof.
  intros l sub r h Hlid.
  destruct Hlid as [Hr Hwest].
  unfold reconnect_split.
  rewrite nth_error_app2 by (rewrite reconnect_left_length; lia).
  rewrite reconnect_left_length.
  replace (length l + length sub - length l)%nat with (length sub) by lia.
  rewrite nth_error_app2 by lia.
  replace (length sub - length sub)%nat with 0%nat by lia.
  unfold reconnect_right.
  destruct (excluded_middle_informative (initial_lid r)) as [Hlid | Hlid].
  - reflexivity.
  - exfalso. apply Hlid. now split.
Qed.

(* 右蓋から二つ以上離れた通常版の出現は、右蓋の blocker 列に入る。 *)
Lemma ordinary_far_from_initial_lid_in_blockers :
  forall l sub r h j ordinary,
    initial_lid r ->
    nth_error (ordinary_reconnect_split l sub r h) j = Some ordinary ->
    (S (length l + length sub) < j
     \/ S j < length l + length sub)%nat ->
    In ordinary (initial_lid_blockers l sub r h).
Proof.
  intros l sub r h j ordinary [Hr Hwest] Hnth Hfar.
  unfold ordinary_reconnect_split in Hnth.
  rewrite app_assoc in Hnth.
  unfold initial_lid_blockers, nonadjacent_sides.
  rewrite in_app_iff.
  destruct Hfar as [Hright | Hleft].
  - right.
    rewrite nth_error_app2 in Hnth.
    2: rewrite length_app, reconnect_segs_length; lia.
    rewrite length_app, reconnect_segs_length in Hnth.
    set (k := (j - (length l + length sub))%nat) in *.
    assert (Hk : (1 < k)%nat) by (unfold k; lia).
    destruct k as [|[|k]]; [lia | lia |].
    destruct (reconnect_segs l sub r h r) as [|a [|b tail]] eqn:HrightList.
    { simpl in Hnth. discriminate. }
    { simpl in Hnth. discriminate. }
    simpl in Hnth |- *.
    now apply nth_error_In in Hnth.
  - left.
    assert (HnthPrefix :
        nth_error (reconnect_segs l sub r h l ++ sub) j = Some ordinary).
    { rewrite nth_error_app1 in Hnth.
      - exact Hnth.
      - rewrite length_app, reconnect_segs_length. lia. }
    apply nth_error_In with (n := j).
    rewrite nth_error_removelast_before_last.
    + exact HnthPrefix.
    + rewrite length_app, reconnect_segs_length. exact Hleft.
Qed.

(* 左蓋は、その添字から二つ以上離れた安全版セグメントの長方形を
   blocker として避ける。この枝では蓋自身の長方形分離を要求しない。 *)
Lemma reconnect_split_terminal_lid_avoids_far_body :
  forall ds l sub r h i j lid other p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    terminal_lid l ->
    i = (length l - 1)%nat ->
    nth_error (reconnect_split l sub r h) i = Some lid ->
    nth_error (reconnect_split l sub r h) j = Some other ->
    (S i < j \/ S j < i)%nat ->
    onSegment lid p ->
    onSegment other p ->
    False.
Proof.
  intros ds l sub r h i j lid other p Hsub Hconn Hmono Hh Hsparse
    Hembed Hext Hlid Hi HlidNth HotherNth Hfar HlidPoint HotherPoint.
  subst i.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
  { eapply operate_endpoints_reconnectable; eauto. }
  destruct (reconnect_split_nth_witnesses l sub r h j other HotherNth)
    as [old [ordinary [Hold Hordinary]]].
  assert (Hbox : same_segment_box ordinary other).
  { exact (proj1 (ordinary_safe_nth_same_box
                    l sub r h j old ordinary other Hsub Hconn Hmono Hh
                    Hsparse Hwhole (ex_intro _ ds Hembed) Hext Hrec
                    Hold Hordinary HotherNth)). }
  assert (Hchosen : lid = choose_terminal_lid l sub r h).
  { pose proof (reconnect_split_terminal_lid_nth l sub r h Hlid) as Hnth.
    rewrite HlidNth in Hnth. now injection Hnth. }
  subst lid.
  pose proof (choose_terminal_lid_spec
                l sub r h Hsub Hconn Hmono Hh Hsparse Hwhole
                (ex_intro _ ds Hembed) Hext Hlid) as Hspec.
  destruct Hspec as [_ [_ Havoid]].
  eapply (Havoid ordinary p).
  - eapply ordinary_far_from_terminal_lid_in_blockers; eauto.
  - apply (same_segment_box_contains other ordinary p).
    + destruct Hbox as [Hinit Hterm]. split; symmetry; assumption.
    + now apply segment_in_rect_or_endpoints.
  - exact HlidPoint.
Qed.

(* 右蓋についての双対。選択した蓋の曲線本体が、非隣接な安全版の
   端点長方形を避けることを blocker 仕様から取り出す。 *)
Lemma reconnect_split_initial_lid_avoids_far_body :
  forall ds l sub r h i j lid other p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    initial_lid r ->
    i = (length l + length sub)%nat ->
    nth_error (reconnect_split l sub r h) i = Some lid ->
    nth_error (reconnect_split l sub r h) j = Some other ->
    (S i < j \/ S j < i)%nat ->
    onSegment lid p ->
    onSegment other p ->
    False.
Proof.
  intros ds l sub r h i j lid other p Hsub Hconn Hmono Hh Hsparse
    Hembed Hext Hlid Hi HlidNth HotherNth Hfar HlidPoint HotherPoint.
  subst i.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
  { eapply operate_endpoints_reconnectable; eauto. }
  destruct (reconnect_split_nth_witnesses l sub r h j other HotherNth)
    as [old [ordinary [Hold Hordinary]]].
  assert (Hbox : same_segment_box ordinary other).
  { exact (proj1 (ordinary_safe_nth_same_box
                    l sub r h j old ordinary other Hsub Hconn Hmono Hh
                    Hsparse Hwhole (ex_intro _ ds Hembed) Hext Hrec
                    Hold Hordinary HotherNth)). }
  assert (Hchosen : lid = choose_initial_lid l sub r h).
  { pose proof (reconnect_split_initial_lid_nth l sub r h Hlid) as Hnth.
    rewrite HlidNth in Hnth. now injection Hnth. }
  subst lid.
  pose proof (choose_initial_lid_spec
                l sub r h Hsub Hconn Hmono Hh Hsparse Hwhole
                (ex_intro _ ds Hembed) Hext Hlid) as Hspec.
  destruct Hspec as [_ [_ Havoid]].
  eapply (Havoid ordinary p).
  - eapply ordinary_far_from_initial_lid_in_blockers; eauto.
  - apply (same_segment_box_contains other ordinary p).
    + destruct Hbox as [Hinit Hterm]. split; symmetry; assumption.
    + now apply segment_in_rect_or_endpoints.
  - exact HlidPoint.
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

(* 三分割列の一出現を、左外部・左接続・sub・右接続・右外部の
   五種類へ、値ではなく添字を保ったまま分類する。 *)
Inductive split_occurrence
    (l sub r : list Segment) (i : nat) (seg : Segment) : Prop :=
| SplitOccLeftOuter :
    (i < length l - 1)%nat ->
    nth_error l i = Some seg ->
    split_occurrence l sub r i seg
| SplitOccLeftBoundary :
    l <> [] ->
    i = (length l - 1)%nat ->
    seg = last_segment l ->
    split_occurrence l sub r i seg
| SplitOccSub :
    forall k,
      (k < length sub)%nat ->
      i = (length l + k)%nat ->
      nth_error sub k = Some seg ->
      split_occurrence l sub r i seg
| SplitOccRightBoundary :
    r <> [] ->
    i = (length l + length sub)%nat ->
    seg = hd_segment r ->
    split_occurrence l sub r i seg
| SplitOccRightOuter :
    forall k,
      (0 < k)%nat ->
      i = (length l + length sub + k)%nat ->
      nth_error r k = Some seg ->
      split_occurrence l sub r i seg.

Lemma nth_error_split_occurrence :
  forall l sub r i seg,
    nth_error (l ++ sub ++ r) i = Some seg ->
    split_occurrence l sub r i seg.
Proof.
  intros l sub r i seg Hnth.
  destruct (Nat.lt_ge_cases i (length l)) as [Hil | Hil].
  - assert (HnthL : nth_error l i = Some seg).
    { rewrite nth_error_app1 in Hnth by exact Hil. exact Hnth. }
    destruct (Nat.eq_dec i (length l - 1)%nat) as [Hi | Hi].
    + assert (Hlne : l <> []).
      { intro Hnil. rewrite Hnil in HnthL. destruct i; discriminate. }
      apply SplitOccLeftBoundary.
      * exact Hlne.
      * exact Hi.
      * subst i.
        assert (Hlast :
            nth_error l (length l - 1) = Some (last_segment l)).
        { unfold last_segment. now apply nth_error_last. }
        rewrite HnthL in Hlast. now injection Hlast.
    + apply SplitOccLeftOuter; [lia | exact HnthL].
  - set (k := (i - length l)%nat).
    assert (HnthTail : nth_error (sub ++ r) k = Some seg).
    { unfold k. rewrite nth_error_app2 in Hnth by lia. exact Hnth. }
    destruct (Nat.lt_ge_cases k (length sub)) as [Hks | Hks].
    + apply (SplitOccSub l sub r i seg k); [exact Hks | unfold k; lia |].
      rewrite nth_error_app1 in HnthTail by exact Hks. exact HnthTail.
    + set (q := (k - length sub)%nat).
      assert (HnthR : nth_error r q = Some seg).
      { unfold q. rewrite nth_error_app2 in HnthTail by lia. exact HnthTail. }
      assert (Hik : i = (length l + k)%nat) by (unfold k; lia).
      assert (Hkq : k = (length sub + q)%nat) by (unfold q; lia).
      destruct q as [|q].
      * assert (Hrne : r <> []).
        { intro Hnil. rewrite Hnil in HnthR. discriminate. }
        apply SplitOccRightBoundary.
        -- exact Hrne.
        -- lia.
        -- destruct r as [|a r']; [contradiction |].
           simpl in HnthR. injection HnthR as <-. reflexivity.
      * apply (SplitOccRightOuter l sub r i seg (S q)).
        -- lia.
        -- lia.
        -- exact HnthR.
Qed.

(* sub の一セグメントの端点は、全体の x 範囲と y-bbox に入る。 *)
Lemma sub_member_endpoint_bounds :
  forall sub t,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    In t sub ->
    (rx0 (rect_of sub) <= fst (init t) <= rx1 (rect_of sub)
     /\ ry0 (bbox_of sub) <= snd (init t) <= ry1 (bbox_of sub))
    /\
    (rx0 (rect_of sub) <= fst (term t) <= rx1 (rect_of sub)
     /\ ry0 (bbox_of sub) <= snd (term t) <= ry1 (bbox_of sub)).
Proof.
  intros sub t Hsub Hconn Hmono Ht.
  assert (HinitOn : onSegmentlist sub (init t)).
  { exists t. split; [exact Ht | apply onInit]. }
  assert (HtermOn : onSegmentlist sub (term t)).
  { exists t. split; [exact Ht | apply onTerm]. }
  pose proof (x_monotone_sub_point_in_x_range
                sub (init t) Hsub Hconn Hmono HinitOn) as Hix.
  pose proof (x_monotone_sub_point_in_x_range
                sub (term t) Hsub Hconn Hmono HtermOn) as Htx.
  pose proof (bbox_of_bounds sub (init t) HinitOn) as Hiy.
  pose proof (bbox_of_bounds sub (term t) HtermOn) as Hty.
  unfold in_sub_x_range in Hix, Htx.
  exact (conj (conj Hix Hiy) (conj Htx Hty)).
Qed.

(* sub 全体から上下左右に離れた端点長方形は、sub の各セグメントの
   端点長方形とも同じ軸方向に厳密分離する。 *)
Lemma endpoint_box_separated_from_sub_separates_member :
  forall sub outside inside,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    In inside sub ->
    endpoint_box_separated_from_sub sub (init outside) (term outside) ->
    endpoint_rectangles_axis_separated outside inside.
Proof.
  intros sub outside inside Hsub Hconn Hmono Hinside Hsep.
  destruct (sub_member_endpoint_bounds
              sub inside Hsub Hconn Hmono Hinside)
    as [[[Hix0 Hix1] [Hiy0 Hiy1]] [[Htx0 Htx1] [Hty0 Hty1]]].
  unfold endpoint_rectangles_axis_separated.
  destruct Hsep as [Habove | [Hbelow | [Hleft | Hright]]].
  - right; right; left.
    unfold both_above_of_sub in Habove. destruct Habove as [Ha Hb].
    change (Rmax (snd (init inside)) (snd (term inside)) <
            Rmin (snd (init outside)) (snd (term outside))).
    apply Rmax_lub_lt; apply Rmin_glb_lt; lra.
  - right; right; right.
    unfold both_below_of_sub in Hbelow. destruct Hbelow as [Ha Hb].
    change (Rmax (snd (init outside)) (snd (term outside)) <
            Rmin (snd (init inside)) (snd (term inside))).
    apply Rmax_lub_lt; apply Rmin_glb_lt; lra.
  - right; left.
    unfold both_left_of_sub in Hleft. destruct Hleft as [Ha Hb].
    change (Rmax (fst (init outside)) (fst (term outside)) <
            Rmin (fst (init inside)) (fst (term inside))).
    apply Rmax_lub_lt; apply Rmin_glb_lt; lra.
  - left.
    unfold both_right_of_sub in Hright. destruct Hright as [Ha Hb].
    change (Rmax (fst (init inside)) (fst (term inside)) <
            Rmin (fst (init outside)) (fst (term outside))).
    apply Rmax_lub_lt; apply Rmin_glb_lt; lra.
Qed.

Definition split_boundary_occurrence
    (l sub r : list Segment) (i : nat) (seg : Segment) : Prop :=
  (l <> [] /\ i = (length l - 1)%nat /\ seg = last_segment l)
  \/ (r <> [] /\ i = (length l + length sub)%nat /\ seg = hd_segment r).

(* 境界出現でなければ、五分解の残りは sub 内か左右の非隣接部分である。 *)
Lemma split_occurrence_nonboundary :
  forall l sub r i seg,
    split_occurrence l sub r i seg ->
    ~ split_boundary_occurrence l sub r i seg ->
    In seg (nonadjacent_sides l r) \/ In seg sub.
Proof.
  intros l sub r i seg Hocc Hnot.
  destruct Hocc as
    [Hbefore HnthL | Hl Hi -> | k Hks Hi HnthS |
     Hr Hi -> | k Hk Hi HnthR].
  - left. unfold nonadjacent_sides. rewrite in_app_iff. left.
    apply nth_error_In with (n := i).
    rewrite nth_error_removelast_before_last.
    + exact HnthL.
    + lia.
  - exfalso. apply Hnot. left. repeat split; assumption.
  - right. now apply nth_error_In in HnthS.
  - exfalso. apply Hnot. right. repeat split; assumption.
  - left. unfold nonadjacent_sides. rewrite in_app_iff. right.
    destruct r as [|a r']; [destruct k; discriminate |].
    destruct k as [|k]; [lia |].
    simpl in HnthR |- *.
    now apply nth_error_In in HnthR.
Qed.

Lemma endpoint_rectangles_axis_separated_sym : forall s t,
  endpoint_rectangles_axis_separated s t ->
  endpoint_rectangles_axis_separated t s.
Proof.
  intros s t Hsep. unfold endpoint_rectangles_axis_separated in *. tauto.
Qed.

Lemma same_boxes_preserve_axis_separation : forall old_s old_t new_s new_t,
  same_segment_box old_s new_s ->
  same_segment_box old_t new_t ->
  endpoint_rectangles_axis_separated old_s old_t ->
  endpoint_rectangles_axis_separated new_s new_t.
Proof.
  intros old_s old_t new_s new_t Hs Ht Hsep.
  unfold endpoint_rectangles_axis_separated in *.
  rewrite <- (same_segment_box_rect old_s new_s Hs).
  rewrite <- (same_segment_box_rect old_t new_t Ht).
  exact Hsep.
Qed.

(* sub のセグメントは端点が固定されるため、通常再接続版でも同じ
   端点長方形を持つ。 *)
Lemma ordinary_sub_member_same_box :
  forall l sub r h old ordinary,
    In old sub ->
    init ordinary = operate_point l sub r h (init old) ->
    term ordinary = operate_point l sub r h (term old) ->
    same_segment_box old ordinary.
Proof.
  intros l sub r h old ordinary Hold Hinit Hterm.
  unfold same_segment_box. split.
  - rewrite Hinit, operate_sub_endpoint; [reflexivity |].
    exists old. split; [exact Hold | now left].
  - rewrite Hterm, operate_sub_endpoint; [reflexivity |].
    exists old. split; [exact Hold | now right].
Qed.

(* 非隣接外部セグメントの通常再接続長方形は、sub のどの一セグメント
   の長方形とも軸方向に分離する。 *)
Lemma ordinary_nonadjacent_vs_sub_member_separated :
  forall l sub r h old outside inside,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    In old (nonadjacent_sides l r) ->
    In inside sub ->
    init outside = operate_point l sub r h (init old) ->
    term outside = operate_point l sub r h (term old) ->
    endpoint_rectangles_axis_separated outside inside.
Proof.
  intros l sub r h old outside inside Hsub Hconn Hmono Hh Hsparse Hwhole
    Hembedded Hext Hold Hinside Hinit Hterm.
  apply endpoint_box_separated_from_sub_separates_member
    with (sub := sub); try assumption.
  rewrite Hinit, Hterm.
  eapply operated_nonadjacent_endpoints_separated; eauto.
Qed.

(* 左右の接続境界を含まない場合は、外部同士・外部と sub・sub 同士の
   三種類だけであり、既存の端点順序保存と固定性から分離が従う。 *)
Lemma ordinary_nonboundary_far_rectangles_separated :
  forall ds l sub r h i j old_s old_t ordinary_s ordinary_t,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    nth_error (l ++ sub ++ r) i = Some old_s ->
    nth_error (l ++ sub ++ r) j = Some old_t ->
    nth_error (ordinary_reconnect_split l sub r h) i = Some ordinary_s ->
    nth_error (ordinary_reconnect_split l sub r h) j = Some ordinary_t ->
    (S i < j \/ S j < i)%nat ->
    ~ split_boundary_occurrence l sub r i old_s ->
    ~ split_boundary_occurrence l sub r j old_t ->
    endpoint_rectangles_axis_separated ordinary_s ordinary_t.
Proof.
  intros ds l sub r h i j old_s old_t ordinary_s ordinary_t
    Hsub Hconn Hmono Hh Hsparse Hembed Hext
    HoldS HoldT HordinaryS HordinaryT Hfar HnotS HnotT.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
  { eapply operate_endpoints_reconnectable; eauto. }
  pose proof (ordinary_reconnect_split_nth_spec
                l sub r h i old_s ordinary_s Hsub Hconn Hmono Hsparse
                Hwhole (ex_intro _ ds Hembed) Hrec HoldS HordinaryS)
    as [_ [HinitS HtermS]].
  pose proof (ordinary_reconnect_split_nth_spec
                l sub r h j old_t ordinary_t Hsub Hconn Hmono Hsparse
                Hwhole (ex_intro _ ds Hembed) Hrec HoldT HordinaryT)
    as [_ [HinitT HtermT]].
  pose proof (split_occurrence_nonboundary
                l sub r i old_s
                (nth_error_split_occurrence l sub r i old_s HoldS) HnotS)
    as [HoutsideS | HinsideS];
  pose proof (split_occurrence_nonboundary
                l sub r j old_t
                (nth_error_split_occurrence l sub r j old_t HoldT) HnotT)
    as [HoutsideT | HinsideT].
  - pose proof (sparse_far_rectangles_axis_separated
                  (l ++ sub ++ r) i j old_s old_t
                  Hsparse HoldS HoldT Hfar) as HoldSep.
    eapply (operated_endpoint_rectangles_axis_separated
              l sub r h i j old_s old_t ordinary_s ordinary_t
              Hsub Hconn Hmono Hsparse Hwhole (ex_intro _ ds Hembed) Hext
              (proj1 Hh) HoldS HoldT Hfar HinitS HtermS HinitT HtermT).
    + exact (nonadjacent_endpoint_not_on_sub
               l sub r old_s (init old_s) Hsparse HoutsideS (or_introl eq_refl)).
    + exact (nonadjacent_endpoint_not_on_sub
               l sub r old_s (term old_s) Hsparse HoutsideS (or_intror eq_refl)).
    + exact (nonadjacent_endpoint_not_on_sub
               l sub r old_t (init old_t) Hsparse HoutsideT (or_introl eq_refl)).
    + exact (nonadjacent_endpoint_not_on_sub
               l sub r old_t (term old_t) Hsparse HoutsideT (or_intror eq_refl)).
    + exact HoldSep.
  - eapply (same_boxes_preserve_axis_separation
              ordinary_s old_t ordinary_s ordinary_t).
    + split; reflexivity.
    + eapply ordinary_sub_member_same_box; eauto.
    + exact (ordinary_nonadjacent_vs_sub_member_separated
               l sub r h old_s ordinary_s old_t Hsub Hconn Hmono Hh Hsparse
               Hwhole (ex_intro _ ds Hembed) Hext HoutsideS HinsideT
               HinitS HtermS).
  - eapply (same_boxes_preserve_axis_separation
              old_s ordinary_t ordinary_s ordinary_t).
    + eapply ordinary_sub_member_same_box; eauto.
    + split; reflexivity.
    + apply endpoint_rectangles_axis_separated_sym.
      exact (ordinary_nonadjacent_vs_sub_member_separated
               l sub r h old_t ordinary_t old_s Hsub Hconn Hmono Hh Hsparse
               Hwhole (ex_intro _ ds Hembed) Hext HoutsideT HinsideS
               HinitT HtermT).
  - exact (same_boxes_preserve_axis_separation
             old_s old_t ordinary_s ordinary_t
             (ordinary_sub_member_same_box
                l sub r h old_s ordinary_s HinsideS HinitS HtermS)
             (ordinary_sub_member_same_box
                l sub r h old_t ordinary_t HinsideT HinitT HtermT)
             (sparse_far_rectangles_axis_separated
                (l ++ sub ++ r) i j old_s old_t
                Hsparse HoldS HoldT Hfar)).
Qed.

(* 非隣接出現の二端点について、上側の端点が sub 上でなければ、
   分類順序と正の移動量が元の厳密な上下順序を保存する。 *)
Lemma operate_preserves_far_endpoint_vertical_order :
  forall l sub r h i j s t ps pt,
    sub <> [] ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    0 < h ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (l ++ sub ++ r) j = Some t ->
    (S i < j \/ S j < i)%nat ->
    segment_x_ranges_overlap s t ->
    endpoint_of_seg s ps ->
    endpoint_of_seg t pt ->
    ~ onSegmentlist sub pt ->
    snd ps < snd pt ->
    snd (operate_point l sub r h ps) < snd (operate_point l sub r h pt).
Proof.
  intros l sub r h i j s t ps pt Hsub Hmono Hsparse Hembed Hext Hh
    Hs Ht Hfar Hoverlap Hps Hpt HptNotSub Hy.
  unfold operate_point.
  eapply shift_preserves_strict_vertical_order; [exact Hh | exact Hy |].
  exact (classified_nonadjacent_endpoint_order
           l sub r
           (classify_spec l sub r Hsub Hmono Hsparse Hembed Hext)
           i j s t ps pt Hs Ht Hfar Hoverlap Hps Hpt
           HptNotSub (Rlt_le _ _ Hy)).
Qed.

Lemma nth_error_sub_in_split : forall (l sub r : list Segment) k s,
  nth_error sub k = Some s ->
  nth_error (l ++ sub ++ r) (length l + k) = Some s.
Proof.
  intros l sub r k s Hnth.
  assert (Hk : (k < length sub)%nat) by now apply nth_error_lt in Hnth.
  rewrite app_assoc.
  rewrite nth_error_app1 by (rewrite length_app; lia).
  rewrite nth_error_app2 by lia.
  replace (length l + k - length l)%nat with k by lia.
  exact Hnth.
Qed.

Lemma nth_error_left_boundary_in_split : forall (l sub r : list Segment),
  l <> [] ->
  nth_error (l ++ sub ++ r) (length l - 1) = Some (last_segment l).
Proof.
  intros l sub r Hl.
  rewrite app_assoc.
  rewrite nth_error_app1.
  2: rewrite length_app; destruct l; [contradiction | simpl; lia].
  rewrite nth_error_app1 by (destruct l; [contradiction | simpl; lia]).
  unfold last_segment. now apply nth_error_last.
Qed.

Lemma nth_error_right_boundary_in_split : forall (l sub r : list Segment),
  r <> [] ->
  nth_error (l ++ sub ++ r) (length l + length sub) = Some (hd_segment r).
Proof.
  intros l sub r Hr.
  rewrite app_assoc.
  rewrite nth_error_app2 by (rewrite length_app; lia).
  rewrite length_app.
  replace (length l + length sub - (length l + length sub))%nat with 0%nat by lia.
  destruct r; [contradiction | reflexivity].
Qed.

(* 左接続セグメントの外側端点は、隣接時には [dc]、それ以外では
   closed sparse により sub 上へ戻れない。 *)
Lemma terminal_outer_endpoint_not_on_sub :
  forall ds l sub r,
    l <> [] ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    ~ onSegmentlist sub (init (last_segment l)).
Proof.
  intros ds l sub r Hl Hsparse Hembed [t [Ht Hon]].
  destruct (in_app_app sub t Ht) as [sl [sr Hsub]].
  subst sub.
  assert (HtSub : nth_error (sl ++ t :: sr) (length sl) = Some t).
  { rewrite nth_error_app2 by lia.
    replace (length sl - length sl)%nat with 0%nat by lia. reflexivity. }
  assert (HtWhole :
      nth_error (l ++ (sl ++ t :: sr) ++ r) (length l + length sl) = Some t).
  { now apply nth_error_sub_in_split. }
  assert (HbWhole :
      nth_error (l ++ (sl ++ t :: sr) ++ r) (length l - 1) =
        Some (last_segment l)).
  { now apply nth_error_left_boundary_in_split. }
  destruct sl as [|a sl'].
  - simpl in HtWhole, HbWhole, Hembed, Hsparse, Hon.
    replace (length l + 0)%nat with (length l) in HtWhole by lia.
    assert (Hnext : S (length l - 1) = length l) by
      (destruct l; [contradiction | simpl; lia]).
    destruct Hembed as [sc [_ Hcurve]].
    destruct (embed_scurve_adjacent_data
                sc (l ++ (t :: sr) ++ r) (length l - 1)
                (last_segment l) t Hcurve HbWhole)
      as [psb [pst [HembB [HembT [Hdc Hjoin]]]]].
    { rewrite Hnext. exact HtWhole. }
    pose proof (adjacent_not_intersect_except_junction
                  psb pst (last_segment l) t (init (last_segment l))
                  Hdc HembB HembT Hjoin (onInit _) Hon) as Heq.
    exact (neq_init_term (last_segment l) Heq).
  - assert (Hfar : (S (length l - 1) < length l + length (a :: sl'))%nat).
    { destruct l; [contradiction | simpl; lia]. }
    destruct (nth_error_far_in_nonadjacent_sides
                (l ++ ((a :: sl') ++ t :: sr) ++ r)
                (length l + length (a :: sl')) (length l - 1)
                t (last_segment l) HtWhole HbWhole (or_intror Hfar))
      as [before [after [Hsplit Hin]]].
    pose proof (Hsparse before t after Hsplit) as [_ Hrect].
    eapply (Hrect (last_segment l) (init (last_segment l)) Hin).
    + apply segment_in_rect_or_endpoints, onInit.
    + change (in_segment_rect_or_endpoints t (init (last_segment l))).
      now apply segment_in_rect_or_endpoints.
Qed.

(* 右接続セグメントについての双対。 *)
Lemma initial_outer_endpoint_not_on_sub :
  forall ds l sub r,
    r <> [] ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    ~ onSegmentlist sub (term (hd_segment r)).
Proof.
  intros ds l sub r Hr Hsparse Hembed [t [Ht Hon]].
  destruct (in_app_app sub t Ht) as [sl [sr Hsub]].
  subst sub.
  assert (HtSub : nth_error (sl ++ t :: sr) (length sl) = Some t).
  { rewrite nth_error_app2 by lia.
    replace (length sl - length sl)%nat with 0%nat by lia. reflexivity. }
  assert (HtWhole :
      nth_error (l ++ (sl ++ t :: sr) ++ r) (length l + length sl) = Some t).
  { now apply nth_error_sub_in_split. }
  assert (HbWhole :
      nth_error (l ++ (sl ++ t :: sr) ++ r)
        (length l + length (sl ++ t :: sr)) = Some (hd_segment r)).
  { now apply nth_error_right_boundary_in_split. }
  destruct sr using rev_ind.
  - assert (Hnext :
        (S (length l + length sl) = length l + length (sl ++ [t]))%nat) by
      (rewrite length_app; simpl; lia).
    destruct Hembed as [sc [_ Hcurve]].
    destruct (embed_scurve_adjacent_data
                sc (l ++ (sl ++ [t]) ++ r) (length l + length sl)
                t (hd_segment r) Hcurve HtWhole)
      as [pst [psb [HembT [HembB [Hdc Hjoin]]]]].
    { rewrite Hnext. exact HbWhole. }
    pose proof (adjacent_not_intersect_except_junction
                  pst psb t (hd_segment r) (term (hd_segment r))
                  Hdc HembT HembB Hjoin Hon (onTerm _)) as Heq.
    apply (neq_init_term (hd_segment r)).
    rewrite <- Hjoin, <- Heq. reflexivity.
  - assert (Hfar :
        (S (length l + length sl) <
         length l + length (sl ++ t :: (sr ++ [x])))%nat).
    { rewrite (length_app sl (t :: (sr ++ [x]))).
      simpl. rewrite (length_app sr [x]). simpl. lia. }
    destruct (nth_error_far_in_nonadjacent_sides
                (l ++ (sl ++ t :: (sr ++ [x])) ++ r)
                (length l + length sl)
                (length l + length (sl ++ t :: (sr ++ [x])))
                t (hd_segment r) HtWhole HbWhole (or_introl Hfar))
      as [before [after [Hsplit Hin]]].
    pose proof (Hsparse before t after Hsplit) as [_ Hrect].
    eapply (Hrect (hd_segment r) (term (hd_segment r)) Hin).
    + apply segment_in_rect_or_endpoints, onTerm.
    + change (in_segment_rect_or_endpoints t (term (hd_segment r))).
      now apply segment_in_rect_or_endpoints.
Qed.

Lemma split_left_outer_in_nonadjacent : forall (l sub r : list Segment) i s,
  (i < length l - 1)%nat ->
  nth_error l i = Some s ->
  In s (nonadjacent_sides l r).
Proof.
  intros l sub r i s Hi Hnth.
  unfold nonadjacent_sides. rewrite in_app_iff. left.
  apply nth_error_In with (n := i).
  rewrite nth_error_removelast_before_last; [exact Hnth | lia].
Qed.

Lemma split_right_outer_in_nonadjacent : forall (l sub r : list Segment) k s,
  (0 < k)%nat ->
  nth_error r k = Some s ->
  In s (nonadjacent_sides l r).
Proof.
  intros l sub r k s Hk Hnth.
  unfold nonadjacent_sides. rewrite in_app_iff. right.
  destruct r as [|a r']; [destruct k; discriminate |].
  destruct k as [|k]; [lia |].
  simpl in Hnth |- *. now apply nth_error_In in Hnth.
Qed.

(* x 単調で連結な列では、先頭以外のセグメント始点は全体始点より右にある。 *)
Lemma x_monotone_nth_init_after_head : forall sub k s,
  connected sub ->
  x_monotone_segs sub ->
  nth_error sub k = Some s ->
  (0 < k)%nat ->
  fst (init (hd_segment sub)) < fst (init s).
Proof.
  induction sub as [|a tail IH]; intros k s Hconn Hmono Hnth Hk.
  { destruct k; discriminate. }
  destruct k as [|k]; [lia |].
  destruct tail as [|b tail']; [destruct k; discriminate |].
  simpl in Hnth.
  assert (Hab : term a = init b).
  { apply (Hconn 0%nat a b); reflexivity. }
  pose proof (Hmono a ltac:(now left)) as Ha.
  destruct k as [|k].
  - simpl in Hnth. injection Hnth as <-. simpl.
    change (fst (init a) < fst (term a)) in Ha.
    rewrite Hab in Ha. exact Ha.
  - assert (HconnTail : connected (b :: tail')).
    { intros n u v Hu Hv. apply (Hconn (S n) u v); simpl; assumption. }
    assert (HmonoTail : x_monotone_segs (b :: tail')).
    { intros u Hu. apply Hmono. now right. }
    pose proof (IH (S k) s HconnTail HmonoTail Hnth ltac:(lia)) as Htail.
    simpl in Htail |- *.
    change (fst (init a) < fst (term a)) in Ha.
    rewrite Hab in Ha. lra.
Qed.

(* 末尾以外のセグメント終点は全体終点より左にある。 *)
Lemma x_monotone_nth_term_before_last : forall sub k s,
  connected sub ->
  x_monotone_segs sub ->
  nth_error sub k = Some s ->
  (k < length sub - 1)%nat ->
  fst (term s) < fst (term (last_segment sub)).
Proof.
  induction sub as [|a tail IH]; intros k s Hconn Hmono Hnth Hk.
  { destruct k; discriminate. }
  destruct tail as [|b tail']; [simpl in Hk; lia |].
  assert (Hab : term a = init b).
  { apply (Hconn 0%nat a b); reflexivity. }
  assert (HconnTail : connected (b :: tail')).
  { intros n u v Hu Hv. apply (Hconn (S n) u v); simpl; assumption. }
  assert (HmonoTail : x_monotone_segs (b :: tail')).
  { intros u Hu. apply Hmono. now right. }
  assert (Hlast : last_segment (a :: b :: tail') = last_segment (b :: tail')).
  { change (last_segment ([a] ++ b :: tail') = last_segment (b :: tail')).
    apply last_app_nonnil. discriminate. }
  destruct k as [|k].
  - simpl in Hnth. injection Hnth as <-. rewrite Hlast.
    pose proof (connected_x_monotone_endpoints
                  (b :: tail') ltac:(discriminate) HconnTail HmonoTail) as Htail.
    simpl in Htail. rewrite Hab. exact Htail.
  - simpl in Hnth. rewrite Hlast.
    apply (IH k s HconnTail HmonoTail Hnth).
    simpl in Hk |- *. lia.
Qed.

Lemma ordinary_terminal_boundary_far_rectangles_separated :
  forall ds l sub r h j other ordinary_b ordinary_o,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    l <> [] ->
    nth_error (l ++ sub ++ r) j = Some other ->
    nth_error (ordinary_reconnect_split l sub r h) (length l - 1) =
      Some ordinary_b ->
    nth_error (ordinary_reconnect_split l sub r h) j = Some ordinary_o ->
    (S (length l - 1) < j \/ S j < length l - 1)%nat ->
    ~ reconnect_split_lid_index l sub r (length l - 1) ->
    ~ reconnect_split_lid_index l sub r j ->
    endpoint_rectangles_axis_separated ordinary_b ordinary_o.
Proof.
  intros ds l sub r h j other ordinary_b ordinary_o
    Hsub Hconn Hmono Hh Hsparse Hembed Hext Hl
    Hother HordinaryB HordinaryO Hfar HnotLidB HnotLidO.
  set (b := last_segment l).
  assert (Hb : nth_error (l ++ sub ++ r) (length l - 1) = Some b).
  { unfold b. now apply nth_error_left_boundary_in_split. }
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
  { eapply operate_endpoints_reconnectable; eauto. }
  pose proof (ordinary_reconnect_split_nth_spec
                l sub r h (length l - 1) b ordinary_b
                Hsub Hconn Hmono Hsparse Hwhole (ex_intro _ ds Hembed) Hrec
                Hb HordinaryB) as [_ [HinitB HtermB]].
  pose proof (ordinary_reconnect_split_nth_spec
                l sub r h j other ordinary_o
                Hsub Hconn Hmono Hsparse Hwhole (ex_intro _ ds Hembed) Hrec
                Hother HordinaryO) as [_ [HinitO HtermO]].
  assert (HnotTerminal : ~ terminal_lid l).
  { intro Hlid. apply HnotLidB. left. now split. }
  assert (HeastB : fst (init b) < fst (term b)).
  { destruct (total_order_T (fst (init b)) (fst (term b)))
      as [[Hlt | Heq] | Hgt]; [exact Hlt | |].
    - exfalso. apply (neq_init_term_x b). exact Heq.
    - exfalso. apply HnotTerminal. split; [exact Hl | exact Hgt]. }
  assert (Htail : sub ++ r <> []).
  { destruct sub; [contradiction | discriminate]. }
  destruct (embed_listDir_app_boundary_data ds l (sub ++ r) Hl Htail Hembed)
    as [psb [pst [HembB [HembT [Hdc Hjoin0]]]]].
  assert (Hhd : hd_segment (sub ++ r) = hd_segment sub).
  { symmetry. unfold hd_segment. now apply hd_app. }
  assert (Hjoin : term b = init (hd_segment sub)).
  { unfold b. now rewrite <- Hhd. }
  assert (Hfixed : operate_point l sub r h (term b) = term b).
  { apply operate_sub_endpoint. rewrite Hjoin.
    exists (hd_segment sub). split.
    - destruct sub; [contradiction | now left].
    - now left. }
  assert (HouterNotSub : ~ onSegmentlist sub (init b)).
  { unfold b. eapply terminal_outer_endpoint_not_on_sub; eauto. }
  assert (Hexternal :
      forall k t t',
        nth_error (l ++ sub ++ r) k = Some t ->
        nth_error (ordinary_reconnect_split l sub r h) k = Some t' ->
        (S (length l - 1) < k \/ S k < length l - 1)%nat ->
        In t (nonadjacent_sides l r) ->
        endpoint_rectangles_axis_separated ordinary_b t').
  { intros k t t' Ht Ht' Hfar' Hin.
    pose proof (ordinary_reconnect_split_nth_spec
                  l sub r h k t t' Hsub Hconn Hmono Hsparse Hwhole
                  (ex_intro _ ds Hembed) Hrec Ht Ht') as [_ [HinitT HtermT]].
    pose proof (sparse_far_rectangles_axis_separated
                  (l ++ sub ++ r) (length l - 1) k b t
                  Hsparse Hb Ht Hfar') as Hsep.
    assert (HtInitNotSub : ~ onSegmentlist sub (init t)).
    { exact (nonadjacent_endpoint_not_on_sub
               l sub r t (init t) Hsparse Hin (or_introl eq_refl)). }
    assert (HtTermNotSub : ~ onSegmentlist sub (term t)).
    { exact (nonadjacent_endpoint_not_on_sub
               l sub r t (term t) Hsparse Hin (or_intror eq_refl)). }
    unfold endpoint_rectangles_axis_separated in Hsep |- *.
    destruct (classic (rx1 (rect_of [t]) < rx0 (rect_of [b]))) as [Hx | Hx].
    - left. change (Rmax (fst (init t')) (fst (term t')) <
                         Rmin (fst (init ordinary_b)) (fst (term ordinary_b))).
      change (Rmax (fst (init t)) (fst (term t)) <
              Rmin (fst (init b)) (fst (term b))) in Hx.
      rewrite HinitB, HtermB, HinitT, HtermT, !operate_point_fst. exact Hx.
    - destruct (classic (rx1 (rect_of [b]) < rx0 (rect_of [t]))) as [Hx' | Hx'].
      + right; left.
        change (Rmax (fst (init ordinary_b)) (fst (term ordinary_b)) <
                       Rmin (fst (init t')) (fst (term t'))).
        change (Rmax (fst (init b)) (fst (term b)) <
                Rmin (fst (init t)) (fst (term t))) in Hx'.
        rewrite HinitB, HtermB, HinitT, HtermT, !operate_point_fst. exact Hx'.
      + assert (Hoverlap : segment_x_ranges_overlap b t).
        { unfold segment_x_ranges_overlap. apply conj; apply Rnot_lt_le; assumption. }
        destruct Hsep as [Hbad | [Hbad' | [HtBelow | HbBelow]]];
          try contradiction.
        * right; right; left.
          change (Rmax (snd (init t)) (snd (term t)) <
                  Rmin (snd (init b)) (snd (term b))) in HtBelow.
          change (Rmax (snd (init t')) (snd (term t')) <
                  Rmin (snd (init ordinary_b)) (snd (term ordinary_b))).
          rewrite HinitB, HtermB, HinitT, HtermT.
          assert (HfarRev : (S k < length l - 1 \/ S (length l - 1) < k)%nat)
            by tauto.
          assert (HoverlapRev : segment_x_ranges_overlap t b).
          { unfold segment_x_ranges_overlap in *. tauto. }
          assert (HtoOuter : forall p,
              endpoint_of_seg t p ->
              snd (operate_point l sub r h p) <
              snd (operate_point l sub r h (init b))).
          { intros p Hp.
            assert (Hy : snd p < snd (init b)).
            { destruct Hp as [-> | ->];
                pose proof (Rmax_l (snd (init t)) (snd (term t)));
                pose proof (Rmax_r (snd (init t)) (snd (term t)));
                pose proof (Rmin_l (snd (init b)) (snd (term b))); lra. }
            exact (operate_preserves_far_endpoint_vertical_order
                     l sub r h k (length l - 1) t b p (init b)
                     Hsub Hmono Hsparse (ex_intro _ ds Hembed) Hext
                     (proj1 Hh) Ht Hb HfarRev HoverlapRev Hp
                     (or_introl eq_refl) HouterNotSub Hy). }
          assert (HtoFixed : forall p,
              endpoint_of_seg t p ->
              snd (operate_point l sub r h p) <
              snd (operate_point l sub r h (term b))).
          { intros p Hp.
            assert (HpWhole : endpoint_of (l ++ sub ++ r) p).
            { exists t. split; [now apply nth_error_In in Ht | exact Hp]. }
            assert (HpBelow : snd p < ry0 (rect_of [b])).
            { change (snd p < Rmin (snd (init b)) (snd (term b))).
              destruct Hp as [-> | ->];
              pose proof (Rmax_l (snd (init t)) (snd (term t)));
              pose proof (Rmax_r (snd (init t)) (snd (term t))); lra. }
            pose proof (operated_endpoint_below_terminal_stays_below
                          l sub r h p Hsub Hmono Hsparse
                          (ex_intro _ ds Hembed) Hext (Rlt_le _ _ (proj1 Hh))
                          Hl HpWhole HpBelow) as Hop.
            change (snd (operate_point l sub r h p) <
                    Rmin (snd (init b)) (snd (term b))) in Hop.
            rewrite Hfixed. eapply Rlt_le_trans; [exact Hop | apply Rmin_r]. }
          apply Rmax_lub_lt; apply Rmin_glb_lt.
          -- apply HtoOuter. now left.
          -- apply HtoFixed. now left.
          -- apply HtoOuter. now right.
          -- apply HtoFixed. now right.
        * right; right; right.
          change (Rmax (snd (init b)) (snd (term b)) <
                  Rmin (snd (init t)) (snd (term t))) in HbBelow.
          change (Rmax (snd (init ordinary_b)) (snd (term ordinary_b)) <
                  Rmin (snd (init t')) (snd (term t'))).
          rewrite HinitB, HtermB, HinitT, HtermT.
          assert (HfromBoundary : forall pb pt,
              endpoint_of_seg b pb -> endpoint_of_seg t pt ->
              snd (operate_point l sub r h pb) <
              snd (operate_point l sub r h pt)).
          { intros pb pt Hpb Hpt.
            assert (HptNotSub : ~ onSegmentlist sub pt).
            { destruct Hpt as [-> | ->]; assumption. }
            assert (Hy : snd pb < snd pt).
            { destruct Hpb as [-> | ->]; destruct Hpt as [-> | ->];
                pose proof (Rmax_l (snd (init b)) (snd (term b)));
                pose proof (Rmax_r (snd (init b)) (snd (term b)));
                pose proof (Rmin_l (snd (init t)) (snd (term t)));
                pose proof (Rmin_r (snd (init t)) (snd (term t))); lra. }
            exact (operate_preserves_far_endpoint_vertical_order
                     l sub r h (length l - 1) k b t pb pt
                     Hsub Hmono Hsparse (ex_intro _ ds Hembed) Hext
                     (proj1 Hh) Hb Ht Hfar' Hoverlap Hpb Hpt HptNotSub Hy). }
          apply Rmax_lub_lt; apply Rmin_glb_lt;
            apply HfromBoundary; [now left | now left | now left | now right |
                                  now right | now left | now right | now right]. }
  destruct (nth_error_split_occurrence l sub r j other Hother) as
    [Hleft HnthLeft | Hl' Hj -> | k Hks Hj HnthSub |
     Hr Hj -> | k Hk Hj HnthRight].
  - apply (Hexternal j other ordinary_o Hother HordinaryO Hfar).
    now apply split_left_outer_in_nonadjacent with (i := j).
  - exfalso. subst j. lia.
  - assert (Hkpos : (0 < k)%nat) by (subst j; destruct Hfar; lia).
    assert (Hafter : fst (init (hd_segment sub)) < fst (init other)).
    { eapply x_monotone_nth_init_after_head; eauto. }
    right; left.
    change (Rmax (fst (init ordinary_b)) (fst (term ordinary_b)) <
            Rmin (fst (init ordinary_o)) (fst (term ordinary_o))).
    rewrite HinitB, HtermB, HinitO, HtermO, !operate_point_fst.
    pose proof (Hmono other (nth_error_In _ _ HnthSub)) as HeastO.
    change (fst (init other) < fst (term other)) in HeastO.
    pose proof (f_equal fst Hjoin) as HjoinX.
    rewrite Rmax_right, Rmin_left by lra. lra.
  - assert (HnotInitial : ~ initial_lid r).
    { intro Hlid. apply HnotLidO. right. now split. }
    assert (HeastO : fst (init (hd_segment r)) < fst (term (hd_segment r))).
    { destruct (total_order_T
                  (fst (init (hd_segment r))) (fst (term (hd_segment r))))
        as [[Hlt | Heq] | Hgt]; [exact Hlt | |].
      - exfalso. apply (neq_init_term_x (hd_segment r)). exact Heq.
      - exfalso. apply HnotInitial. split; assumption. }
    assert (Hprefix : l ++ sub <> []).
    { intro Hnil. apply app_eq_nil in Hnil as [_ Hnil]. contradiction. }
    assert (Hembed' : embed_listDir ds ((l ++ sub) ++ r)).
    { rewrite <- app_assoc. exact Hembed. }
    destruct (embed_listDir_app_boundary_data ds (l ++ sub) r Hprefix Hr Hembed')
      as [pss [psr [HembS [HembR [HdcR HjoinR0]]]]].
    assert (Hlast : last_segment (l ++ sub) = last_segment sub).
    { now apply last_app_nonnil. }
    assert (HjoinR : term (last_segment sub) = init (hd_segment r)).
    { now rewrite <- Hlast. }
    pose proof (connected_x_monotone_endpoints sub Hsub Hconn Hmono) as HsubX.
    right; left.
    change (Rmax (fst (init ordinary_b)) (fst (term ordinary_b)) <
            Rmin (fst (init ordinary_o)) (fst (term ordinary_o))).
    rewrite HinitB, HtermB, HinitO, HtermO, !operate_point_fst.
    pose proof (f_equal fst Hjoin) as HjoinX.
    pose proof (f_equal fst HjoinR) as HjoinRX.
    rewrite Rmax_right, Rmin_left by lra. lra.
  - apply (Hexternal j other ordinary_o Hother HordinaryO Hfar).
    now apply split_right_outer_in_nonadjacent with (k := k).
Qed.

Lemma ordinary_initial_boundary_far_rectangles_separated :
  forall ds l sub r h j other ordinary_b ordinary_o,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    r <> [] ->
    nth_error (l ++ sub ++ r) j = Some other ->
    nth_error (ordinary_reconnect_split l sub r h)
      (length l + length sub) = Some ordinary_b ->
    nth_error (ordinary_reconnect_split l sub r h) j = Some ordinary_o ->
    (S (length l + length sub) < j
     \/ S j < length l + length sub)%nat ->
    ~ reconnect_split_lid_index l sub r (length l + length sub) ->
    ~ reconnect_split_lid_index l sub r j ->
    endpoint_rectangles_axis_separated ordinary_b ordinary_o.
Proof.
  intros ds l sub r h j other ordinary_b ordinary_o
    Hsub Hconn Hmono Hh Hsparse Hembed Hext Hr
    Hother HordinaryB HordinaryO Hfar HnotLidB HnotLidO.
  set (b := hd_segment r).
  assert (Hb :
      nth_error (l ++ sub ++ r) (length l + length sub) = Some b).
  { unfold b. now apply nth_error_right_boundary_in_split. }
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
  { eapply operate_endpoints_reconnectable; eauto. }
  pose proof (ordinary_reconnect_split_nth_spec
                l sub r h (length l + length sub) b ordinary_b
                Hsub Hconn Hmono Hsparse Hwhole (ex_intro _ ds Hembed) Hrec
                Hb HordinaryB) as [_ [HinitB HtermB]].
  pose proof (ordinary_reconnect_split_nth_spec
                l sub r h j other ordinary_o
                Hsub Hconn Hmono Hsparse Hwhole (ex_intro _ ds Hembed) Hrec
                Hother HordinaryO) as [_ [HinitO HtermO]].
  assert (HnotInitial : ~ initial_lid r).
  { intro Hlid. apply HnotLidB. right. now split. }
  assert (HeastB : fst (init b) < fst (term b)).
  { destruct (total_order_T (fst (init b)) (fst (term b)))
      as [[Hlt | Heq] | Hgt]; [exact Hlt | |].
    - exfalso. apply (neq_init_term_x b). exact Heq.
    - exfalso. apply HnotInitial. split; [exact Hr | exact Hgt]. }
  assert (Hprefix : l ++ sub <> []).
  { intro Hnil. apply app_eq_nil in Hnil as [_ Hnil]. contradiction. }
  assert (Hembed' : embed_listDir ds ((l ++ sub) ++ r)).
  { rewrite <- app_assoc. exact Hembed. }
  destruct (embed_listDir_app_boundary_data ds (l ++ sub) r Hprefix Hr Hembed')
    as [pst [psb [HembT [HembB [Hdc Hjoin0]]]]].
  assert (Hlast : last_segment (l ++ sub) = last_segment sub).
  { now apply last_app_nonnil. }
  assert (Hjoin : term (last_segment sub) = init b).
  { unfold b. now rewrite <- Hlast. }
  assert (Hfixed : operate_point l sub r h (init b) = init b).
  { apply operate_sub_endpoint. rewrite <- Hjoin.
    exists (last_segment sub). split.
    - apply last_In. exact Hsub.
    - now right. }
  assert (HouterNotSub : ~ onSegmentlist sub (term b)).
  { unfold b. eapply initial_outer_endpoint_not_on_sub; eauto. }
  assert (Hexternal :
      forall k t t',
        nth_error (l ++ sub ++ r) k = Some t ->
        nth_error (ordinary_reconnect_split l sub r h) k = Some t' ->
        (S (length l + length sub) < k
         \/ S k < length l + length sub)%nat ->
        In t (nonadjacent_sides l r) ->
        endpoint_rectangles_axis_separated ordinary_b t').
  { intros k t t' Ht Ht' Hfar' Hin.
    pose proof (ordinary_reconnect_split_nth_spec
                  l sub r h k t t' Hsub Hconn Hmono Hsparse Hwhole
                  (ex_intro _ ds Hembed) Hrec Ht Ht') as [_ [HinitT HtermT]].
    pose proof (sparse_far_rectangles_axis_separated
                  (l ++ sub ++ r) (length l + length sub) k b t
                  Hsparse Hb Ht Hfar') as Hsep.
    assert (HtInitNotSub : ~ onSegmentlist sub (init t)).
    { exact (nonadjacent_endpoint_not_on_sub
               l sub r t (init t) Hsparse Hin (or_introl eq_refl)). }
    assert (HtTermNotSub : ~ onSegmentlist sub (term t)).
    { exact (nonadjacent_endpoint_not_on_sub
               l sub r t (term t) Hsparse Hin (or_intror eq_refl)). }
    unfold endpoint_rectangles_axis_separated in Hsep |- *.
    destruct (classic (rx1 (rect_of [t]) < rx0 (rect_of [b]))) as [Hx | Hx].
    - left. change (Rmax (fst (init t')) (fst (term t')) <
                         Rmin (fst (init ordinary_b)) (fst (term ordinary_b))).
      change (Rmax (fst (init t)) (fst (term t)) <
              Rmin (fst (init b)) (fst (term b))) in Hx.
      rewrite HinitB, HtermB, HinitT, HtermT, !operate_point_fst. exact Hx.
    - destruct (classic (rx1 (rect_of [b]) < rx0 (rect_of [t]))) as [Hx' | Hx'].
      + right; left.
        change (Rmax (fst (init ordinary_b)) (fst (term ordinary_b)) <
                       Rmin (fst (init t')) (fst (term t'))).
        change (Rmax (fst (init b)) (fst (term b)) <
                Rmin (fst (init t)) (fst (term t))) in Hx'.
        rewrite HinitB, HtermB, HinitT, HtermT, !operate_point_fst. exact Hx'.
      + assert (Hoverlap : segment_x_ranges_overlap b t).
        { unfold segment_x_ranges_overlap. apply conj; apply Rnot_lt_le; assumption. }
        destruct Hsep as [Hbad | [Hbad' | [HtBelow | HbBelow]]];
          try contradiction.
        * right; right; left.
          change (Rmax (snd (init t)) (snd (term t)) <
                  Rmin (snd (init b)) (snd (term b))) in HtBelow.
          change (Rmax (snd (init t')) (snd (term t')) <
                  Rmin (snd (init ordinary_b)) (snd (term ordinary_b))).
          rewrite HinitB, HtermB, HinitT, HtermT.
          assert (HfarRev :
              (S k < length l + length sub
               \/ S (length l + length sub) < k)%nat) by tauto.
          assert (HoverlapRev : segment_x_ranges_overlap t b).
          { unfold segment_x_ranges_overlap in *. tauto. }
          assert (HtoOuter : forall p,
              endpoint_of_seg t p ->
              snd (operate_point l sub r h p) <
              snd (operate_point l sub r h (term b))).
          { intros p Hp.
            assert (Hy : snd p < snd (term b)).
            { destruct Hp as [-> | ->];
                pose proof (Rmax_l (snd (init t)) (snd (term t)));
                pose proof (Rmax_r (snd (init t)) (snd (term t)));
                pose proof (Rmin_r (snd (init b)) (snd (term b))); lra. }
            exact (operate_preserves_far_endpoint_vertical_order
                     l sub r h k (length l + length sub) t b p (term b)
                     Hsub Hmono Hsparse (ex_intro _ ds Hembed) Hext
                     (proj1 Hh) Ht Hb HfarRev HoverlapRev Hp
                     (or_intror eq_refl) HouterNotSub Hy). }
          assert (HtoFixed : forall p,
              endpoint_of_seg t p ->
              snd (operate_point l sub r h p) <
              snd (operate_point l sub r h (init b))).
          { intros p Hp.
            assert (HpWhole : endpoint_of (l ++ sub ++ r) p).
            { exists t. split; [now apply nth_error_In in Ht | exact Hp]. }
            assert (HpBelow : snd p < ry0 (rect_of [b])).
            { change (snd p < Rmin (snd (init b)) (snd (term b))).
              destruct Hp as [-> | ->];
                pose proof (Rmax_l (snd (init t)) (snd (term t)));
                pose proof (Rmax_r (snd (init t)) (snd (term t))); lra. }
            pose proof (operated_endpoint_below_initial_stays_below
                          l sub r h p Hsub Hmono Hsparse
                          (ex_intro _ ds Hembed) Hext (Rlt_le _ _ (proj1 Hh))
                          Hr HpWhole HpBelow) as Hop.
            change (snd (operate_point l sub r h p) <
                    Rmin (snd (init b)) (snd (term b))) in Hop.
            rewrite Hfixed. eapply Rlt_le_trans; [exact Hop | apply Rmin_l]. }
          apply Rmax_lub_lt; apply Rmin_glb_lt.
          -- apply HtoFixed. now left.
          -- apply HtoOuter. now left.
          -- apply HtoFixed. now right.
          -- apply HtoOuter. now right.
        * right; right; right.
          change (Rmax (snd (init b)) (snd (term b)) <
                  Rmin (snd (init t)) (snd (term t))) in HbBelow.
          change (Rmax (snd (init ordinary_b)) (snd (term ordinary_b)) <
                  Rmin (snd (init t')) (snd (term t'))).
          rewrite HinitB, HtermB, HinitT, HtermT.
          assert (HfromBoundary : forall pb pt,
              endpoint_of_seg b pb -> endpoint_of_seg t pt ->
              snd (operate_point l sub r h pb) <
              snd (operate_point l sub r h pt)).
          { intros pb pt Hpb Hpt.
            assert (HptNotSub : ~ onSegmentlist sub pt).
            { destruct Hpt as [-> | ->]; assumption. }
            assert (Hy : snd pb < snd pt).
            { destruct Hpb as [-> | ->]; destruct Hpt as [-> | ->];
                pose proof (Rmax_l (snd (init b)) (snd (term b)));
                pose proof (Rmax_r (snd (init b)) (snd (term b)));
                pose proof (Rmin_l (snd (init t)) (snd (term t)));
                pose proof (Rmin_r (snd (init t)) (snd (term t))); lra. }
            exact (operate_preserves_far_endpoint_vertical_order
                     l sub r h (length l + length sub) k b t pb pt
                     Hsub Hmono Hsparse (ex_intro _ ds Hembed) Hext
                     (proj1 Hh) Hb Ht Hfar' Hoverlap Hpb Hpt HptNotSub Hy). }
          apply Rmax_lub_lt; apply Rmin_glb_lt;
            apply HfromBoundary; [now left | now left | now left | now right |
                                  now right | now left | now right | now right]. }
  destruct (nth_error_split_occurrence l sub r j other Hother) as
    [Hleft HnthLeft | Hl Hj -> | k Hks Hj HnthSub |
     Hr' Hj -> | k Hk Hj HnthRight].
  - apply (Hexternal j other ordinary_o Hother HordinaryO Hfar).
    now apply split_left_outer_in_nonadjacent with (i := j).
  - assert (HnotTerminal : ~ terminal_lid l).
    { intro Hlid. apply HnotLidO. left. now split. }
    assert (HeastO : fst (init (last_segment l)) < fst (term (last_segment l))).
    { destruct (total_order_T
                  (fst (init (last_segment l))) (fst (term (last_segment l))))
        as [[Hlt | Heq] | Hgt]; [exact Hlt | |].
      - exfalso. apply (neq_init_term_x (last_segment l)). exact Heq.
      - exfalso. apply HnotTerminal. split; assumption. }
    assert (Htail : sub ++ r <> []).
    { destruct sub; [contradiction | discriminate]. }
    destruct (embed_listDir_app_boundary_data ds l (sub ++ r) Hl Htail Hembed)
      as [psl [pss [HembL [HembS [HdcL HjoinL0]]]]].
    assert (Hhd : hd_segment (sub ++ r) = hd_segment sub).
    { symmetry. unfold hd_segment. now apply hd_app. }
    assert (HjoinL : term (last_segment l) = init (hd_segment sub)).
    { now rewrite <- Hhd. }
    pose proof (connected_x_monotone_endpoints sub Hsub Hconn Hmono) as HsubX.
    left.
    change (Rmax (fst (init ordinary_o)) (fst (term ordinary_o)) <
            Rmin (fst (init ordinary_b)) (fst (term ordinary_b))).
    rewrite HinitB, HtermB, HinitO, HtermO, !operate_point_fst.
    pose proof (f_equal fst HjoinL) as HjoinLX.
    pose proof (f_equal fst Hjoin) as HjoinX.
    rewrite Rmax_right, Rmin_left by lra. lra.
  - assert (HkBefore : (k < length sub - 1)%nat).
    { subst j. destruct Hfar; lia. }
    assert (Hbefore : fst (term other) < fst (term (last_segment sub))).
    { eapply x_monotone_nth_term_before_last; eauto. }
    left.
    change (Rmax (fst (init ordinary_o)) (fst (term ordinary_o)) <
            Rmin (fst (init ordinary_b)) (fst (term ordinary_b))).
    rewrite HinitB, HtermB, HinitO, HtermO, !operate_point_fst.
    pose proof (Hmono other (nth_error_In _ _ HnthSub)) as HeastO.
    change (fst (init other) < fst (term other)) in HeastO.
    pose proof (f_equal fst Hjoin) as HjoinX.
    rewrite Rmax_right, Rmin_left by lra. lra.
  - exfalso. subst j. lia.
  - apply (Hexternal j other ordinary_o Hother HordinaryO Hfar).
    now apply split_right_outer_in_nonadjacent with (k := k).
Qed.

(* 残る本質的な枝：sub に隣接する非蓋セグメントと、二つ以上離れた
   出現との垂直分離を、固定接続点を含めて保存する。 *)
Lemma ordinary_boundary_far_rectangles_separated :
  forall ds l sub r h i j old_s old_t ordinary_s ordinary_t,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    nth_error (l ++ sub ++ r) i = Some old_s ->
    nth_error (l ++ sub ++ r) j = Some old_t ->
    nth_error (ordinary_reconnect_split l sub r h) i = Some ordinary_s ->
    nth_error (ordinary_reconnect_split l sub r h) j = Some ordinary_t ->
    (S i < j \/ S j < i)%nat ->
    (split_boundary_occurrence l sub r i old_s
     \/ split_boundary_occurrence l sub r j old_t) ->
    ~ reconnect_split_lid_index l sub r i ->
    ~ reconnect_split_lid_index l sub r j ->
    endpoint_rectangles_axis_separated ordinary_s ordinary_t.
Proof.
  intros ds l sub r h i j old_s old_t ordinary_s ordinary_t
    Hsub Hconn Hmono Hh Hsparse Hembed Hext
    HoldS HoldT HordinaryS HordinaryT Hfar Hboundary HnotLidS HnotLidT.
  destruct Hboundary as [HboundaryS | HboundaryT].
  - destruct HboundaryS as [[Hl [Hi Hs]] | [Hr [Hi Hs]]].
    + subst i old_s.
      exact (ordinary_terminal_boundary_far_rectangles_separated
               ds l sub r h j old_t ordinary_s ordinary_t
               Hsub Hconn Hmono Hh Hsparse Hembed Hext Hl
               HoldT HordinaryS HordinaryT Hfar HnotLidS HnotLidT).
    + subst i old_s.
      exact (ordinary_initial_boundary_far_rectangles_separated
               ds l sub r h j old_t ordinary_s ordinary_t
               Hsub Hconn Hmono Hh Hsparse Hembed Hext Hr
               HoldT HordinaryS HordinaryT Hfar HnotLidS HnotLidT).
  - apply endpoint_rectangles_axis_separated_sym.
    destruct HboundaryT as [[Hl [Hj Ht]] | [Hr [Hj Ht]]].
    + subst j old_t.
      exact (ordinary_terminal_boundary_far_rectangles_separated
               ds l sub r h i old_s ordinary_t ordinary_s
               Hsub Hconn Hmono Hh Hsparse Hembed Hext Hl
               HoldS HordinaryT HordinaryS ltac:(tauto) HnotLidT HnotLidS).
    + subst j old_t.
      exact (ordinary_initial_boundary_far_rectangles_separated
               ds l sub r h i old_s ordinary_t ordinary_s
               Hsub Hconn Hmono Hh Hsparse Hembed Hext Hr
               HoldS HordinaryT HordinaryS ltac:(tauto) HnotLidT HnotLidS).
Qed.

(* 蓋でない二出現では、元の sparse な長方形分離を端点操作後へ運ぶ。
   水平分離、sub 内、sub 隣接境界、外部端点の各場合分けをここに集約する。 *)
Lemma ordinary_nonlid_far_rectangles_separated :
  forall ds l sub r h i j old_s old_t ordinary_s ordinary_t,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    nth_error (l ++ sub ++ r) i = Some old_s ->
    nth_error (l ++ sub ++ r) j = Some old_t ->
    nth_error (ordinary_reconnect_split l sub r h) i = Some ordinary_s ->
    nth_error (ordinary_reconnect_split l sub r h) j = Some ordinary_t ->
    (S i < j \/ S j < i)%nat ->
    ~ reconnect_split_lid_index l sub r i ->
    ~ reconnect_split_lid_index l sub r j ->
    endpoint_rectangles_axis_separated ordinary_s ordinary_t.
Proof.
  intros ds l sub r h i j old_s old_t ordinary_s ordinary_t
    Hsub Hconn Hmono Hh Hsparse Hembed Hext
    HoldS HoldT HordinaryS HordinaryT Hfar HnotLidS HnotLidT.
  destruct (classic (split_boundary_occurrence l sub r i old_s))
    as [HboundaryS | HboundaryS].
  - exact (ordinary_boundary_far_rectangles_separated
             ds l sub r h i j old_s old_t ordinary_s ordinary_t
             Hsub Hconn Hmono Hh Hsparse Hembed Hext
             HoldS HoldT HordinaryS HordinaryT Hfar
             (or_introl HboundaryS) HnotLidS HnotLidT).
  - destruct (classic (split_boundary_occurrence l sub r j old_t))
      as [HboundaryT | HboundaryT].
    + exact (ordinary_boundary_far_rectangles_separated
               ds l sub r h i j old_s old_t ordinary_s ordinary_t
               Hsub Hconn Hmono Hh Hsparse Hembed Hext
               HoldS HoldT HordinaryS HordinaryT Hfar
               (or_intror HboundaryT) HnotLidS HnotLidT).
    + exact (ordinary_nonboundary_far_rectangles_separated
               ds l sub r h i j old_s old_t ordinary_s ordinary_t
               Hsub Hconn Hmono Hh Hsparse Hembed Hext
               HoldS HoldT HordinaryS HordinaryT Hfar
               HboundaryS HboundaryT).
Qed.

(* 戻る蓋は safe reconnect の blocker 回避、通常セグメントは分類順序を
   用いて処理する。全域の長方形 sparse ではなく曲線本体だけを排除する。 *)
Lemma reconnect_split_nonadjacent_bodies_disjoint :
  forall ds l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    nonadjacent_bodies_disjoint (reconnect_split l sub r h).
Proof.
  intros ds l sub r h Hsub Hconn Hmono Hh Hsparse Hembed Hext.
  unfold nonadjacent_bodies_disjoint.
  intros i j s t p Hs Ht Hfar Hsp Htp.
  destruct (classic (reconnect_split_lid_index l sub r i)) as [Hi | Hi].
  - destruct Hi as [[Hlid Hi] | [Hlid Hi]].
    + eapply reconnect_split_terminal_lid_avoids_far_body; eauto.
    + eapply reconnect_split_initial_lid_avoids_far_body; eauto.
  - destruct (classic (reconnect_split_lid_index l sub r j)) as [Hj | Hj].
    + destruct Hj as [[Hlid Hj] | [Hlid Hj]].
      * eapply (reconnect_split_terminal_lid_avoids_far_body
                  ds l sub r h j i t s p); eauto; lia.
      * eapply (reconnect_split_initial_lid_avoids_far_body
                  ds l sub r h j i t s p); eauto; lia.
    + destruct (reconnect_split_nth_witnesses l sub r h i s Hs)
        as [old_s [ordinary_s [Hold_s Hordinary_s]]].
      destruct (reconnect_split_nth_witnesses l sub r h j t Ht)
        as [old_t [ordinary_t [Hold_t Hordinary_t]]].
      assert (Hsafe_s : s = ordinary_s).
      { exact (reconnect_split_nth_eq_ordinary_unless_lid
                 l sub r h i ordinary_s s Hi Hordinary_s Hs). }
      assert (Hsafe_t : t = ordinary_t).
      { exact (reconnect_split_nth_eq_ordinary_unless_lid
                 l sub r h j ordinary_t t Hj Hordinary_t Ht). }
      subst s t.
      pose proof (ordinary_nonlid_far_rectangles_separated
                    ds l sub r h i j old_s old_t ordinary_s ordinary_t
                    Hsub Hconn Hmono Hh Hsparse Hembed Hext
                    Hold_s Hold_t Hordinary_s Hordinary_t Hfar Hi Hj)
        as Hseparated.
      apply (axis_separated_boxes_avoid
               ordinary_s ordinary_t Hseparated p).
      * now apply segment_in_rect_or_endpoints.
      * now apply segment_in_rect_or_endpoints.
Qed.

(* 具体的な再接続列について、本体・延長線の三種類の衝突を排除して
   開性を得る。初期 sparse 性は各衝突証明書を作る前段でのみ使う。 *)
Lemma reconnect_preserves_open :
  forall l sub r h,
    sub <> [] ->
    positive_bodies_disjoint (reconnect_split l sub r h) ->
    extensions_avoid_positive_bodies (reconnect_split l sub r h) ->
    extensions_disjoint (reconnect_split l sub r h) ->
    ~ close (reconnect_split l sub r h).
Proof.
  intros l sub r h Hsub Hbody Hextbody Hext.
  apply separated_bodies_extensions_open; try assumption.
  intros Hnil.
  unfold reconnect_split in Hnil.
  apply app_eq_nil in Hnil as [_ Hsubr].
  apply app_eq_nil in Hsubr as [Hsubnil _].
  now apply Hsub.
Qed.

(* 再接続後に残す不変量は、sub 周りの局所 sparse 性と開性だけである。 *)
Lemma reconnect_gives_sparse_around_and_open :
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
      (reconnect_right l sub r h)
    /\ ~ close (reconnect_split l sub r h).
Proof.
  intros ds l sub r h Hwhole Hws Hh Hsparse Hembed Hext.
  destruct Hws as [Hne [Hmono HsubOpen]].
  assert (Hconn : connected sub).
  { eapply connected_middle. exact Hwhole. }
  split.
  - apply (reconnect_gives_safe_sparse_around
             ds l sub r h Hwhole).
    + repeat split; assumption.
    + exact Hh.
    + exact Hsparse.
    + exact Hembed.
    + exact Hext.
  - assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
    { exact (operate_endpoints_reconnectable
               l sub r h Hne Hconn Hmono Hh Hsparse Hwhole
               (ex_intro _ ds Hembed) Hext). }
    assert (HsafeEmbed : embed_listDir ds (reconnect_split l sub r h)).
    { eapply reconnect_split_safe_preserves_embed; eauto. }
    assert (Hfar : nonadjacent_bodies_disjoint (reconnect_split l sub r h)).
    { eapply reconnect_split_nonadjacent_bodies_disjoint; eauto. }
    apply (separated_reconnected_curve_open
             ds (reconnect_split l sub r h)).
    + intro Hnil.
      unfold reconnect_split in Hnil.
      apply app_eq_nil in Hnil as [_ Htail].
      apply app_eq_nil in Htail as [Hsub _].
      contradiction.
    + exact HsafeEmbed.
    + exact Hfar.
    + eapply reconnect_split_extensions_avoid_positive_bodies; eauto.
    + eapply reconnect_split_extensions_disjoint; eauto.
Qed.


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

(* 疎な初期埋め込みを回転して sub を x 単調にし、再接続後の局所疎性と
   開性を得る。全域 sparse 性はこの結論に含めない。 *)
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
                l1 sub1 r1 h Hsub1ne HconnSub1 Hx1 Hh Hsparse1 HconnAll1
                (ex_intro _ (ds1 ++ sub_ds ++ ds2) Hall1) Hext1)
    as HrecAll1.
  assert (HlocalOpen :
      sparse_around
        (reconnect_left l1 sub1 r1 h) sub1
        (reconnect_right l1 sub1 r1 h)
      /\ ~ close (reconnect_split l1 sub1 r1 h)).
  { apply reconnect_gives_sparse_around_and_open
      with (ds := ds1 ++ sub_ds ++ ds2); assumption. }
  exists (reconnect_left l1 sub1 r1 h),
         (reconnect_right l1 sub1 r1 h),
         sub1.
  split.
  - eapply reconnects_list_preserves_embed; [|exact Hl1].
    eapply reconnect_left_reconnects_after; eauto.
  - split; [exact Hsub1 |].
    split.
    + eapply reconnects_list_preserves_embed; [|exact Hr1].
      eapply reconnect_right_reconnects_after; eauto.
    + split.
      * eapply reconnect_split_safe_preserves_embed; eauto.
      * split.
        -- exact (proj2 HlocalOpen).
        -- split.
           ++ exact (proj1 HlocalOpen).
           ++ exact Hsub1ne.
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
