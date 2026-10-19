Require Import Admissible.
Require Import Reduction.
Require Import Stdlib.Reals.Reals.
Require Import Embed.
Require Import PrimitiveSegment.
Require Import Segment.
Require Import SegmentsTranslation.
Require Import ListExt.
Require Import Sparse.ReconnectWholeProof.
Require Import Sparse.PMPEmbedding.
Require Import Stdlib.Logic.ClassicalDescription.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.

(* AdmissibleDirs について成り立ってほしい性質と、それに必要な補題。 *)

(* PrimitiveSegment の90度回転。Direction と dc を保つ四つの対応を、
   scurve の抽象的な回転とは独立に有限場合分けで扱う。 *)
Local Definition quarter_turn_primitive (p : PrimitiveSegment) : PrimitiveSegment :=
  match p with
  | (n, e, cx) => (n, w, cc)
  | (n, e, cc) => (n, w, cx)
  | (n, w, cx) => (s, w, cx)
  | (n, w, cc) => (s, w, cc)
  | (s, e, cx) => (n, e, cx)
  | (s, e, cc) => (n, e, cc)
  | (s, w, cx) => (s, e, cc)
  | (s, w, cc) => (s, e, cx)
  end.

Local Definition rotate_primitive (g : Rot) (p : PrimitiveSegment) : PrimitiveSegment :=
  match g with
  | R0 => p
  | R90 => quarter_turn_primitive p
  | R180 => quarter_turn_primitive (quarter_turn_primitive p)
  | R270 =>
      quarter_turn_primitive
        (quarter_turn_primitive (quarter_turn_primitive p))
  end.

Local Definition quarter_turn_dir (d : Dir) : Dir :=
  match d with
  | Hor e => Ver n
  | Hor w => Ver s
  | Ver n => Hor w
  | Ver s => Hor e
  end.

Local Definition rotate_dir (g : Rot) (d : Dir) : Dir :=
  match g with
  | R0 => d
  | R90 => quarter_turn_dir d
  | R180 => quarter_turn_dir (quarter_turn_dir d)
  | R270 => quarter_turn_dir (quarter_turn_dir (quarter_turn_dir d))
  end.

Local Definition follows_dir (d : Dir) (p : PrimitiveSegment) : Prop :=
  match d with
  | Ver v => V_of p = v
  | Hor h => H_of p = h
  end.

Lemma rotate_primitive_orn : forall g p,
  orn (rotate_primitive g p) = orn p.
Proof.
  intros g [[v h] c]. destruct g, v, h, c; reflexivity.
Qed.

Lemma rotate_primitive_dc : forall g p q,
  dc p q -> dc (rotate_primitive g p) (rotate_primitive g q).
Proof.
  intros g [[v1 h1] c1] [[v2 h2] c2] Hdc.
  destruct v1, h1, c1, v2, h2, c2;
    inversion Hdc; subst; destruct g; simpl; constructor.
Qed.

Lemma dc_successor_of_direction_unique : forall p q1 q2,
  dc p q1 -> dc p q2 -> orn q1 = orn q2 -> q1 = q2.
Proof.
  intros [[v h] c] [[v1 h1] c1] [[v2 h2] c2] H1 H2 Hdir.
  destruct v, h, c, v1, h1, c1, v2, h2, c2;
    inversion H1; inversion H2; subst; simpl in Hdir;
    try discriminate; reflexivity.
Qed.

Lemma same_orn_has_primitive_rotation : forall p q,
  orn p = orn q -> exists g, q = rotate_primitive g p.
Proof.
  intros [[v1 h1] c1] [[v2 h2] c2].
  destruct v1, h1, c1, v2, h2, c2; simpl; intros H;
    try discriminate;
    first [exists R0; reflexivity
          | exists R90; reflexivity
          | exists R180; reflexivity
          | exists R270; reflexivity].
Qed.

Lemma is_scurve_tail : forall p ps,
  is_scurve (p :: ps) -> is_scurve ps.
Proof.
  intros p ps H. inversion H; assumption.
Qed.

Lemma same_direction_scurve_lists_rotate : forall g p q ps qs,
  is_scurve (p :: ps) ->
  is_scurve (q :: qs) ->
  map orn (p :: ps) = map orn (q :: qs) ->
  q = rotate_primitive g p ->
  q :: qs = map (rotate_primitive g) (p :: ps).
Proof.
  intros g p q ps. revert g p q.
  induction ps as [|p' ps IH]; intros g p q qs Hps Hqs Hdir Hhead.
  - destruct qs as [|q' qs].
    + simpl. now rewrite Hhead.
    + simpl in Hdir. injection Hdir as _ Htail. discriminate Htail.
  - destruct qs as [|q' qs].
    + simpl in Hdir. injection Hdir as _ Htail. discriminate Htail.
    + assert (HtailDir : map orn (p' :: ps) = map orn (q' :: qs)).
      { exact (f_equal (@tl Direction) Hdir). }
      assert (HnextDir : orn p' = orn q').
      { pose proof (f_equal (hd Plus) HtailDir) as H.
        simpl in H. exact H. }
      assert (Hdc1 : dc p p').
      { eapply is_scurve_adjacent_dc with (ps := p :: p' :: ps) (i := 0%nat);
          eauto; reflexivity. }
      assert (Hdc2 : dc q q').
      { eapply is_scurve_adjacent_dc with (ps := q :: q' :: qs) (i := 0%nat);
          eauto; reflexivity. }
      assert (Hnext : q' = rotate_primitive g p').
      { apply (dc_successor_of_direction_unique
                 q q' (rotate_primitive g p')); [exact Hdc2 | |].
        - rewrite Hhead. now apply rotate_primitive_dc.
        - rewrite rotate_primitive_orn. symmetry. exact HnextDir. }
      assert (HtailCurve1 : is_scurve (p' :: ps)).
      { now apply is_scurve_tail in Hps. }
      assert (HtailCurve2 : is_scurve (q' :: qs)).
      { now apply is_scurve_tail in Hqs. }
      assert (HtailEq :
          q' :: qs = map (rotate_primitive g) (p' :: ps)).
      { eapply IH; eauto. }
      simpl. rewrite Hhead. now f_equal.
Qed.

Lemma follows_dir_rotate : forall g d p,
  follows_dir d p -> follows_dir (rotate_dir g d) (rotate_primitive g p).
Proof.
  intros g d [[v h] c] H.
  destruct g; destruct d as [vd | hd];
    try destruct vd; try destruct hd;
    destruct v; destruct h; destruct c; simpl in *;
    try discriminate; reflexivity.
Qed.

Lemma Forall_follows_dir_rotate : forall g d ps,
  Forall (follows_dir d) ps ->
  Forall (follows_dir (rotate_dir g d))
    (map (rotate_primitive g) ps).
Proof.
  intros g d ps H. induction H; simpl; constructor; auto.
  now apply follows_dir_rotate.
Qed.

Lemma is_one_way_scurve_dir_form : forall sc,
  is_one_way_scurve sc <->
  proj1_sig sc <> [] /\
  exists d, Forall (follows_dir d) (proj1_sig sc).
Proof.
  intros [ps Hcurve]. unfold is_one_way_scurve. simpl. split.
  - intros [Hne Hways]. split; [exact Hne |].
    clear Hcurve Hne.
    destruct Hways as [He | [Hw | [Hn | Hs]]].
    + exists (Hor e). induction He as [|p ps Hp Hps IH].
      * constructor.
      * constructor; [|exact IH]. destruct Hp as [v [c ->]]. reflexivity.
    + exists (Hor w). induction Hw as [|p ps Hp Hps IH].
      * constructor.
      * constructor; [|exact IH]. destruct Hp as [v [c ->]]. reflexivity.
    + exists (Ver n). induction Hn as [|p ps Hp Hps IH].
      * constructor.
      * constructor; [|exact IH]. destruct Hp as [h [c ->]]. reflexivity.
    + exists (Ver s). induction Hs as [|p ps Hp Hps IH].
      * constructor.
      * constructor; [|exact IH]. destruct Hp as [h [c ->]]. reflexivity.
  - intros [Hne [d Hd]]. split; [exact Hne |].
    destruct d as [v | h]; [destruct v | destruct h].
    + right; right; left. apply Forall_forall. intros [[v' h] c] Hp.
      apply Forall_forall with (x := ((v', h), c)) in Hd; [|exact Hp].
      unfold follows_dir, V_of in Hd. simpl in Hd.
      exists h, c. now rewrite Hd.
    + do 3 right. apply Forall_forall. intros [[v' h] c] Hp.
      apply Forall_forall with (x := ((v', h), c)) in Hd; [|exact Hp].
      unfold follows_dir, V_of in Hd. simpl in Hd.
      exists h, c. now rewrite Hd.
    + left. apply Forall_forall. intros [[v h'] c] Hp.
      apply Forall_forall with (x := ((v, h'), c)) in Hd; [|exact Hp].
      unfold follows_dir, H_of in Hd. simpl in Hd.
      exists v, c. now rewrite Hd.
    + right; left. apply Forall_forall. intros [[v h'] c] Hp.
      apply Forall_forall with (x := ((v, h'), c)) in Hd; [|exact Hp].
      unfold follows_dir, H_of in Hd. simpl in Hd.
      exists v, c. now rewrite Hd.
Qed.

(* 単方向曲線と向き列が同じなら単方向曲線 *)
Lemma is_one_way_same_direction : forall sc1 sc2,
	scurve_to_direction sc1 = scurve_to_direction sc2
	-> is_one_way_scurve sc1
	-> is_one_way_scurve sc2.
Proof.
  intros [ps Hps] [qs Hqs] Hdir Hone.
  apply is_one_way_scurve_dir_form in Hone.
  destruct Hone as [HpsNe [d Hone]]. simpl in *.
  destruct ps as [|p ps]; [contradiction |].
  destruct qs as [|q qs].
  { unfold scurve_to_direction in Hdir. simpl in Hdir. discriminate. }
  unfold scurve_to_direction in Hdir. simpl in Hdir.
  assert (HheadDir : orn p = orn q) by now injection Hdir.
  destruct (same_orn_has_primitive_rotation p q HheadDir) as [g Hg].
  assert (Hlists :
      q :: qs = map (rotate_primitive g) (p :: ps)).
  { eapply same_direction_scurve_lists_rotate; eauto. }
  apply is_one_way_scurve_dir_form. simpl.
  split; [discriminate |].
  exists (rotate_dir g d). rewrite Hlists.
  now apply Forall_follows_dir_rotate.
Qed.

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

(* --------------------------------------------------------------------------- *)
(* extend に関する補題．extend の公理は Segment.v 参照 *)

Lemma extention_split : forall t1 t2 ls,
  let p1 := extend ls t1 in let p2 := extend ls t2 in
  ls <> [] -> t1 <> t2 ->
  (exists u1 u2, u1 <= 0 /\ u2 <= 0 /\ u1 <> u2 /\ p1 = point (hd_segment ls) u1 /\ p2 = point (hd_segment ls) u2)
  \/ (exists u1 u2 s, u1 <= 0 /\ 0 < u2 <= 1 /\ In s ls /\ p1 = point (hd_segment ls) u1 /\ p2 = point s u2)
  \/ (exists u1 u2, u1 <= 0 /\ 1 < u2 /\ p1 = point (hd_segment ls) u1 /\ p2 = point (last_segment ls) u2)
  \/ (exists u1 u2 s, 0 < u1 <= 1 /\ u2 <= 0 /\ In s ls /\ p1 = point s u1 /\ p2 = point (hd_segment ls) u2)
  \/ (exists u1 u2 s, 0 < u1 <= 1 /\ 0 < u2 <= 1 /\ u1 <> u2 /\ In s ls /\ p1 = point s u1 /\ p2 = point s u2)
  \/ (exists u1 u2 s1 s2, 0 < u1 <= 1 /\ 0 < u2 <= 1 /\ In_order s1 s2 ls /\ p1 = point s1 u1 /\ p2 = point s2 u2)
  \/ (exists u1 u2 s1 s2, 0 < u1 <= 1 /\ 0 < u2 <= 1 /\ In_order s2 s1 ls /\ p1 = point s1 u1 /\ p2 = point s2 u2)
  \/ (exists u1 u2 s, 0 < u1 <= 1 /\ 1 < u2 /\ In s ls /\ p1 = point s u1 /\ p2 = point (last_segment ls) u2)
  \/ (exists u1 u2, 1 < u1 /\ u2 <= 0 /\ p1 = point (last_segment ls) u1 /\ p2 = point (hd_segment ls) u2)
  \/ (exists u1 u2 s, 1 < u1 /\ 0 < u2 <= 1 /\ In s ls /\ p1 = point (last_segment ls) u1 /\ p2 = point s u2)
  \/ (exists u1 u2, 1 < u1 /\ 1 < u2 /\ u1 <> u2 /\ p1 = point (last_segment ls) u1 /\ p2 = point (last_segment ls) u2).
Proof.
  intros t1 t2 ls p1 p2 Hne Hneq.
  destruct (extend_repr ls t1 Hne) as [s1 [N1 E1]].
  destruct (extend_repr ls t2 Hne) as [s2 [N2 E2]].
  destruct (extend_param_region ls t1 Hne) as [M1 | [[H1 H1u] | [L1 L1u]]];
  destruct (extend_param_region ls t2 Hne) as [M2 | [[H2 H2u] | [L2 L2u]]].
  - destruct (Nat.eq_dec (extend_index ls t1) (extend_index ls t2)) as [I|I].
    + do 4 right; left. subst. assert (s1 = s2) by congruence. subst s2.
      exists (extend_param ls t1), (extend_param ls t2), s1.
      assert (U : extend_param ls t1 <> extend_param ls t2). {
        intro U. apply Hneq. eapply extend_same_piece_injective; eauto. }
      assert (Hin : In s1 ls). { apply nth_error_In in N1; exact N1. }
      tauto.
    + destruct (Nat.lt_ge_cases (extend_index ls t1) (extend_index ls t2)) as [LT|GE].
      * do 5 right; left. exists (extend_param ls t1), (extend_param ls t2), s1, s2.
        assert (O : In_order s1 s2 ls) by (eapply In_order_nth; eauto).
        tauto.
      * do 6 right; left. exists (extend_param ls t1), (extend_param ls t2), s1, s2.
        assert (O : In_order s2 s1 ls) by (eapply In_order_nth; eauto; lia).
        tauto.
  - do 3 right; left. assert (SH : s2 = hd_segment ls). { rewrite H2 in N2. unfold hd_segment. symmetry. eapply nth_error_hd; eauto. }
    subst s2. exists (extend_param ls t1), (extend_param ls t2), s1.
    assert (Hin : In s1 ls). { apply nth_error_In in N1; exact N1. } tauto.
  - do 7 right; left. assert (SL : s2 = last_segment ls). {
      unfold last_segment. assert (K : extend_index ls t2 = (length ls - 1)%nat) by lia.
      rewrite K in N2. pose proof (@nth_error_last Segment ls default_segment Hne) as Q.
      rewrite N2 in Q. injection Q as Q. exact Q. }
    subst s2. exists (extend_param ls t1), (extend_param ls t2), s1.
    assert (Hin : In s1 ls). { apply nth_error_In in N1; exact N1. } tauto.
  - right; left. assert (SH : s1 = hd_segment ls). { rewrite H1 in N1. unfold hd_segment. symmetry. eapply nth_error_hd; eauto. }
    subst s1. exists (extend_param ls t1), (extend_param ls t2), s2.
    assert (Hin : In s2 ls). { apply nth_error_In in N2; exact N2. } tauto.
  - left. assert (A : s1 = hd_segment ls). { rewrite H1 in N1. unfold hd_segment. symmetry. eapply nth_error_hd; eauto. }
    assert (B : s2 = hd_segment ls). { rewrite H2 in N2. unfold hd_segment. symmetry. eapply nth_error_hd; eauto. }
    subst s1; subst s2. exists (extend_param ls t1), (extend_param ls t2).
    assert (U : extend_param ls t1 <> extend_param ls t2). { intro U. apply Hneq. eapply extend_same_piece_injective; [apply Hne | rewrite H1, H2; reflexivity | exact U]. }
    tauto.
  - do 2 right; left. assert (A : s1 = hd_segment ls). { rewrite H1 in N1. unfold hd_segment. symmetry. eapply nth_error_hd; eauto. }
    assert (B : s2 = last_segment ls). { unfold last_segment. assert (K : extend_index ls t2 = (length ls - 1)%nat) by lia.
      rewrite K in N2. pose proof (@nth_error_last Segment ls default_segment Hne) as Q. rewrite N2 in Q. injection Q as Q. exact Q. }
    subst s1; subst s2. exists (extend_param ls t1), (extend_param ls t2). repeat split; assumption.
  - do 9 right; left. assert (A : s1 = last_segment ls). { unfold last_segment. assert (K : extend_index ls t1 = (length ls - 1)%nat) by lia.
      rewrite K in N1. pose proof (@nth_error_last Segment ls default_segment Hne) as Q. rewrite N1 in Q. injection Q as Q. exact Q. }
    subst s1. exists (extend_param ls t1), (extend_param ls t2), s2.
    assert (Hin : In s2 ls). { apply nth_error_In in N2; exact N2. } tauto.
  - do 8 right; left. assert (A : s1 = last_segment ls). { unfold last_segment. assert (K : extend_index ls t1 = (length ls - 1)%nat) by lia.
      rewrite K in N1. pose proof (@nth_error_last Segment ls default_segment Hne) as Q. rewrite N1 in Q. injection Q as Q. exact Q. }
    assert (B : s2 = hd_segment ls). { rewrite H2 in N2. unfold hd_segment. symmetry. eapply nth_error_hd; eauto. }
    subst s1; subst s2. exists (extend_param ls t1), (extend_param ls t2). repeat split; assumption.
  - repeat right. assert (A : s1 = last_segment ls). { unfold last_segment. assert (K : extend_index ls t1 = (length ls - 1)%nat) by lia.
      rewrite K in N1. pose proof (@nth_error_last Segment ls default_segment Hne) as Q. rewrite N1 in Q. injection Q as Q. exact Q. }
    assert (B : s2 = last_segment ls). { unfold last_segment. assert (K : extend_index ls t2 = (length ls - 1)%nat) by lia.
      rewrite K in N2. pose proof (@nth_error_last Segment ls default_segment Hne) as Q. rewrite N2 in Q. injection Q as Q. exact Q. }
    subst s1; subst s2. exists (extend_param ls t1), (extend_param ls t2).
    assert (I : extend_index ls t1 = extend_index ls t2) by lia.
    assert (U : extend_param ls t1 <> extend_param ls t2). { intro U. apply Hneq. eapply extend_same_piece_injective; [apply Hne | exact I | exact U]. }
    tauto.
Qed.

(* 連結した列の非隣接セグメントが一点を共有すれば、延長した曲線は閉。 *)
Lemma two_segs_have_same_point_close : forall s1 s2 p ls,
	connected ls
	-> onSegment s1 p
	-> onSegment s2 p
	-> (exists l1 l2 l3, ls = l1 ++ s1 :: l2 ++ s2 :: l3 /\ l2 <> [])  (* 逆順は不要 *)
	-> close ls.
Proof.
Admitted.

(* 先頭と末尾の延長線が交わっていたら，同じ延長線を持つ曲線は閉 *)
Lemma head_last_cross_close : forall p ls1 ls2,
	ls2 <> []
	-> onHead_extend ls1 p
	-> onLast_extend ls1 p
	-> same_extention_head ls1 ls2
	-> same_extention_last ls1 ls2
	-> close ls2.
Proof.
Admitted.

(* 先頭の延長線が先頭以外のセグメントと交わっていたら，同じ延長線とセグメントを持つ曲線は閉 *)
Lemma head_seg_cross_close : forall p seg ls1 ls2 n,
	onHead_extend ls1 p
	-> In seg ls1
	-> onSegment' seg p
	-> same_extention_head ls1 ls2
	-> nth_error ls2 n = Some seg
	-> (n > 0)%nat
	-> close ls2.
Proof.
Admitted.

(* 末尾の延長線が末尾以外のセグメントと交わっていたら，同じ延長線とセグメントを持つ曲線は閉 *)
Lemma last_seg_cross_close : forall p seg ls1 ls2 n,
	onLast_extend ls1 p
	-> In seg ls1
	-> onSegment' seg p
	-> same_extention_last ls1 ls2
	-> nth_error ls2 n = Some seg
	-> (n < length ls2 - 1)%nat
	-> close ls2.
Proof.
Admitted.

(* １つのセグメントの中（延長部分含め）で交差は起こらない（point の満たすべき性質，仕様） *)
Lemma one_seg_not_cross : forall t1 t2 seg,
	point seg t1 = point seg t2
	-> t1 = t2.
Proof.
	intros t1 t2 seg H. exact (point_injective seg t1 t2 H).
Qed.

(* 接続点での滑らかさを課さず、指定した外側の傾きを持つ連結2セグメントが存在する *)
Definition reconnect_slope_pair
	(p q : Point) (d1 d2 : Direction) (slope_p slope_q : R) : Prop :=
	exists middle slope_left slope_right,
		in_rect (rect_between p q) middle /\
		reconnect_slope p middle d1 slope_p slope_left /\
		reconnect_slope middle q d2 slope_right slope_q.

Axiom reconnect_slope_pair_spec :
  forall p q d1 d2 slope_p slope_q,
    reconnect_slope_pair p q d1 d2 slope_p slope_q <->
    exists s1 s2,
      embed_listDir [d1; d2] [s1; s2]
      /\ init s1 = p
      /\ term s2 = q
      /\ in_rect (rect_between p q) (term s1)
      /\ slope_init s1 = slope_p
      /\ slope_term s2 = slope_q.

Definition same_init_and_term (c1 c2 : list Segment) := 
	init (hd_segment c1) = init (hd_segment c2) 
	/\ term (last_segment c1) = term (last_segment c2).
Definition same_slope_init_and_term (c1 c2 : list Segment) := 
	slope_init (hd_segment c1) = slope_init (hd_segment c2) 
	/\ slope_term (last_segment c1) = slope_term (last_segment c2).

(* 始点と始点での傾きが同じであれば，始点方向への延長線は等しい（slope_init 等の満たすべき性質，仕様） *)
Lemma same_init_then_same_extention_head : forall ls1 ls2,
	let seg1 := hd_segment ls1 in
	let seg2 := hd_segment ls2 in
	init seg1 = init seg2
	-> slope_init seg1 = slope_init seg2
	-> same_extention_head ls1 ls2.
Proof. 
	intros ls1 ls2 Hinit Hslope p.
	unfold same_extention_head, onHead_extend.
	now apply head_extension_determined_by_init_slope.
Qed.

Lemma same_term_then_same_extention_last : forall ls1 ls2,
	let seg1 := last_segment ls1 in
	let seg2 := last_segment ls2 in
	term seg1 = term seg2
	-> slope_term seg1 = slope_term seg2
	-> same_extention_last ls1 ls2.
Proof. 
	intros ls1 ls2 Hterm Hslope p.
	unfold same_extention_last, onLast_extend.
	now apply last_extension_determined_by_term_slope.
Qed.

(* --------------------------------------------------------------------------- *)
(* 許容可能性保持の証明に向けた定義と補題群 *)

Lemma is_one_way_listDir_forall : forall ds,
	is_one_way_listDir ds <-> 
		(forall sc, scurve_to_direction sc = ds -> is_one_way_scurve sc).
Proof.
	intros ds. split.
	- (* -> *) intros [sc' [Hembed Honeway]] sc Hdir.
		eapply is_one_way_same_direction; [ | eassumption].
		congruence.
	- (* <- *) intros H. 
		destruct ds as [ | d ds'].
		+ (* このままでは contradiction にならないか *)
			specialize H with (exist _ [] IsScurveNil).
			unfold scurve_to_direction, is_one_way_scurve in H.
			specialize (H eq_refl).
			simpl in H; destruct H.
			contradiction. 
		+ pose proof (Direction_to_PrimitiveSegment d default_primitive_segment) as [p [Hp _]].
			subst.
			pose proof (direction_scurve_correspondence ds' p) as [sc [_ Hdir]].
			exists sc. split; auto.
Qed. 

Lemma P_is_oneway : is_one_way_listDir [Plus].
Proof. 
	exists (scurve_from_one (n,e,cx)). split.
	- unfold scurve_to_direction. reflexivity.
	- unfold is_one_way_scurve; split.
		+ (* not nil *) simpl. congruence.
		+ (* Forall *) left. constructor; eauto.
Qed.

Lemma PM_is_oneway : is_one_way_listDir [Plus; Minus].
Proof. 
	set (p1 := scurve_from_one (n,e,cx)).
	set (p2 := scurve_from_one (n,e,cc)).
	eexists (exist _ [(n,e,cx); (n,e,cc)] _). split.
	- unfold scurve_to_direction. reflexivity.
	- unfold is_one_way_scurve; split.
		+ (* not nil *) simpl. congruence.
		+ (* Forall *) left. constructor; eauto.
	Unshelve. (* scurve であることの証明 *) 
	simpl. repeat constructor.
Qed.

Lemma PMP_is_oneway : is_one_way_listDir [Plus; Minus; Plus].
Proof.
	set (p1 := scurve_from_one (n,e,cx)).
	set (p2 := scurve_from_one (n,e,cc)).
	eexists (exist _ [(n,e,cx); (n,e,cc); (n,e,cx)] _). split.
	- unfold scurve_to_direction. reflexivity.
	- unfold is_one_way_scurve; split.
		+ (* not nil *) simpl. congruence.
		+ (* Forall *) left. repeat constructor; eauto.
	Unshelve. (* scurve であることの証明 *) 
	simpl. repeat constructor.
Qed.

Lemma PPMM_is_oneway : is_one_way_listDir [Plus; Plus; Minus; Minus].
Proof.
	set (p1 := scurve_from_one (n,e,cx)).
	set (p2 := scurve_from_one (s,e,cx)).
	set (p3 := scurve_from_one (s,e,cc)).
	set (p4 := scurve_from_one (n,e,cc)).
	eexists (exist _ [(n,e,cx); (s,e,cx); (s,e,cc); (n,e,cc)] _). split.
	- unfold scurve_to_direction. reflexivity.
	- unfold is_one_way_scurve; split.
		+ (* not nil *) simpl. congruence.
		+ (* Forall *) left. repeat constructor; eauto.
	Unshelve. (* scurve であることの証明 *)
	simpl. repeat constructor.
Qed.

(* [Plus] 系 is_oneway 補題を，全ての PrimitiveSegment の cx/cc を反転させることで
		[Minus] 系に写す（v は e 側では orn に無関係なので固定のままでよい） *)
Lemma M_is_oneway : is_one_way_listDir [Minus].
Proof.
	exists (scurve_from_one (n,e,cc)). split.
	- unfold scurve_to_direction. reflexivity.
	- unfold is_one_way_scurve; split.
		+ (* not nil *) simpl. congruence.
		+ (* Forall *) left. constructor; eauto.
Qed.

Lemma MP_is_oneway : is_one_way_listDir [Minus; Plus].
Proof.
	set (p1 := scurve_from_one (n,e,cc)).
	set (p2 := scurve_from_one (n,e,cx)).
	eexists (exist _ [(n,e,cc); (n,e,cx)] _). split.
	- unfold scurve_to_direction. reflexivity.
	- unfold is_one_way_scurve; split.
		+ (* not nil *) simpl. congruence.
		+ (* Forall *) left. constructor; eauto.
	Unshelve. (* scurve であることの証明 *)
	simpl. repeat constructor.
Qed.

Lemma MPM_is_oneway : is_one_way_listDir [Minus; Plus; Minus].
Proof.
	set (p1 := scurve_from_one (n,e,cc)).
	set (p2 := scurve_from_one (n,e,cx)).
	eexists (exist _ [(n,e,cc); (n,e,cx); (n,e,cc)] _). split.
	- unfold scurve_to_direction. reflexivity.
	- unfold is_one_way_scurve; split.
		+ (* not nil *) simpl. congruence.
		+ (* Forall *) left. repeat constructor; eauto.
	Unshelve. (* scurve であることの証明 *)
	simpl. repeat constructor.
Qed.

(* PPMM 側は (n,e,cx);(s,e,cx);(s,e,cc);(n,e,cc) を dc で繋いでいた．
		v(=n/s) と c(=cx/cc) を同時に反転（h=e は固定）させると dc の各規則
		（DXtrvN <-> DXtrvS, DIfl は自己双対）はそのまま保たれ，かつ e 側では
		orn は c のみで決まる（cx -> Plus, cc -> Minus）ので，向きは Plus/Minus が
		入れ替わる．よって (s,e,cc);(n,e,cc);(n,e,cx);(s,e,cx) が MMPP の埋め込みになる． *)
Lemma MMPP_is_oneway : is_one_way_listDir [Minus; Minus; Plus; Plus].
Proof.
	set (p1 := scurve_from_one (s,e,cc)).
	set (p2 := scurve_from_one (n,e,cc)).
	set (p3 := scurve_from_one (n,e,cx)).
	set (p4 := scurve_from_one (s,e,cx)).
	eexists (exist _ [(s,e,cc); (n,e,cc); (n,e,cx); (s,e,cx)] _). split.
	- unfold scurve_to_direction. reflexivity.
	- unfold is_one_way_scurve; split.
		+ (* not nil *) simpl. congruence.
		+ (* Forall *) left. repeat constructor; eauto.
	Unshelve. (* scurve であることの証明 *)
	simpl. repeat constructor.
Qed.

Lemma embedding_oneway_listDir : forall ds ls,
	embed_listDir ds ls -> is_one_way_listDir ds -> is_one_way_embedding ls.
Proof.
	intros ds ls H1 H2.
	destruct H1 as [sc [Hdir Hembed]].
	exists sc. split; auto.
	apply (is_one_way_listDir_forall ds); auto.
Qed.

Lemma embedding_one_dir : forall d ls, 
	embed_listDir [d] ls -> exists seg, ls = [seg].
Proof. 
	intros d ls H. 
	apply embedding_listDir_length_consis in H.
	destruct ls as [ | x ls']; try discriminate.
	destruct ls'; try discriminate.
	repeat eexists.
Qed.

Lemma embedding_two_dir : forall d1 d2 ls, 
	embed_listDir [d1; d2] ls -> exists seg1 seg2, ls = [seg1; seg2].
Proof. 
	intros d1 d2 ls H. 
	apply embedding_listDir_length_consis in H.
	destruct ls as [ | x1 ls1]; try discriminate.
	destruct ls1 as [ | x2 ls2]; try discriminate.
	destruct ls2; try discriminate.
	repeat eexists.
Qed.

Lemma embedding_three_dir : forall d1 d2 d3 ls, 
	embed_listDir [d1; d2; d3] ls -> exists seg1 seg2 seg3, ls = [seg1; seg2; seg3].
Proof. 
	intros d1 d2 d3 ls H. 
	apply embedding_listDir_length_consis in H.
	destruct ls as [ | x1 ls1]; try discriminate.
	destruct ls1 as [ | x2 ls2]; try discriminate.
	destruct ls2 as [ | x3 ls3]; try discriminate.
	destruct ls3; try discriminate.
	repeat eexists.
Qed.

Lemma embedding_four_dir : forall d1 d2 d3 d4 ls, 
	embed_listDir [d1; d2; d3; d4] ls -> exists seg1 seg2 seg3 seg4, ls = [seg1; seg2; seg3; seg4].
Proof.
	intros d1 d2 d3 d4 ls H. 
	apply embedding_listDir_length_consis in H.
	destruct ls as [ | x1 ls1]; try discriminate.
	destruct ls1 as [ | x2 ls2]; try discriminate.
	destruct ls2 as [ | x3 ls3]; try discriminate.
	destruct ls3 as [ | x4 ls4]; try discriminate.
	destruct ls4; try discriminate.
	repeat eexists.
Qed.

(* 単方向曲線は開 *)
Lemma oneway_then_open : forall ls, 
	is_one_way_embedding ls -> ~ close ls.
Proof.
Admitted.

(* 最終命題に入力する、全セグメント周りで疎な初期埋め込みの存在。 *)
Lemma AdmissibleDirs_has_sparse_embedding :
  forall ds,
    AdmissibleDirs ds ->
    exists ls,
      embed_listDir ds ls
      /\ sparse_embedding ls
      /\ extensions_disjoint ls.
Admitted.

(* 既存の疎な埋め込みの存在から ++-- 用の prepared 証人を選び直す。
   任意の疎な証人そのものを回転・変形できるとは主張しない。 *)
Lemma sparse_PPMM_can_be_prepared :
  forall ds1 ds2,
    AdmissibleDirs (ds1 ++ [Plus; Plus; Minus; Minus] ++ ds2) ->
    (exists ls,
      embed_listDir (ds1 ++ [Plus; Plus; Minus; Minus] ++ ds2) ls
      /\ sparse_embedding ls
      /\ extensions_disjoint ls) ->
    exists l sub r,
      PreparedSparseEmbedding ds1 [Plus; Plus; Minus; Minus] ds2 l sub r.
Admitted.

Lemma AdmissibleDirs_has_prepared_PPMM :
  forall ds1 ds2,
    AdmissibleDirs (ds1 ++ [Plus; Plus; Minus; Minus] ++ ds2) ->
    exists l sub r,
      PreparedSparseEmbedding ds1 [Plus; Plus; Minus; Minus] ds2 l sub r.
Proof.
  intros ds1 ds2 Hadm.
  eapply sparse_PPMM_can_be_prepared; [exact Hadm |].
  exact (AdmissibleDirs_has_sparse_embedding _ Hadm).
Qed.

(* --++ についても、疎な証人の存在と prepared 証人の選択を分ける。 *)
Lemma sparse_MMPP_can_be_prepared :
  forall ds1 ds2,
    AdmissibleDirs (ds1 ++ [Minus; Minus; Plus; Plus] ++ ds2) ->
    (exists ls,
      embed_listDir (ds1 ++ [Minus; Minus; Plus; Plus] ++ ds2) ls
      /\ sparse_embedding ls
      /\ extensions_disjoint ls) ->
    exists l sub r,
      PreparedSparseEmbedding ds1 [Minus; Minus; Plus; Plus] ds2 l sub r.
Admitted.

Lemma AdmissibleDirs_has_prepared_MMPP :
  forall ds1 ds2,
    AdmissibleDirs (ds1 ++ [Minus; Minus; Plus; Plus] ++ ds2) ->
    exists l sub r,
      PreparedSparseEmbedding ds1 [Minus; Minus; Plus; Plus] ds2 l sub r.
Proof.
  intros ds1 ds2 Hadm.
  eapply sparse_MMPP_can_be_prepared; [exact Hadm |].
  exact (AdmissibleDirs_has_sparse_embedding _ Hadm).
Qed.

(* 二方向部分列で両側の蓋を避けられる初期埋め込みの選択。
   全域 sparse 性と prepared 幾何を同じ証人について要求する。 *)
Lemma AdmissibleDirs_has_prepared_PM :
  forall ds1 ds2,
    AdmissibleDirs (ds1 ++ [Plus; Minus] ++ ds2) ->
    exists l sub r, PreparedSparseEmbedding ds1 [Plus; Minus] ds2 l sub r.
Admitted.

Lemma AdmissibleDirs_has_prepared_MP :
  forall ds1 ds2,
    AdmissibleDirs (ds1 ++ [Minus; Plus] ++ ds2) ->
    exists l sub r, PreparedSparseEmbedding ds1 [Minus; Plus] ds2 l sub r.
Admitted.

(* PMP の terminal 側の蓋除去と端点傾きを満たす幾何学的な証人を選ぶ。
   Up/Fix 分類の整合性は、選択後に classify_pmp_sources_safe で別に示す。 *)
Lemma sparse_PMP_can_be_prepared : forall ds1 ds2,
  AdmissibleDirs (ds1 ++ [Plus; Minus; Plus] ++ ds2) ->
  (exists ls, embed_listDir (ds1 ++ [Plus; Minus; Plus] ++ ds2) ls /\
    sparse_embedding ls /\ extensions_disjoint ls) ->
  exists l sub r, PreparedPMPEmbedding ds1 ds2 l sub r.
Admitted.

(* PMP は全域で三角形疎、簡約部分の端点から作る Plus 側の三角形でも疎。
   両端と端点傾きは、単一の Plus セグメントへ接続できるように選ぶ。 *)
Lemma embed_sparsely_listDir_PMP (ds1 ds2 : list Direction) :
	AdmissibleDirs (ds1 ++ [Plus; Minus; Plus] ++ ds2)
	-> exists l r seg1 seg2 seg3,
		reconnect_slope (init seg1) (term seg3) Plus
			(slope_init seg1) (slope_term seg3) (* 将来的にこの部分を，傾きを保存したまま１つのセグメントに変更できるように *)
		/\ embed_listDir ds1 l
		/\ embed_listDir [Plus; Minus; Plus] [seg1; seg2; seg3]
		/\ embed_listDir ds2 r
		/\ embed_listDir (ds1 ++ [Plus; Minus; Plus] ++ ds2) (l ++ [seg1; seg2; seg3] ++ r)
		/\ sparse_embedding (l ++ [seg1; seg2; seg3] ++ r)
		/\ ~ close (l ++ [seg1; seg2; seg3] ++ r)
		/\ sparse_around_triangle Plus l [seg1; seg2; seg3] r.
Proof.
  intro Hadm.
  destruct (sparse_PMP_can_be_prepared ds1 ds2 Hadm
              (AdmissibleDirs_has_sparse_embedding _ Hadm))
    as [old_l [sub [old_r Hprepared]]].
  assert (Hembed : exists ds, embed_listDir ds (old_l ++ sub ++ old_r)).
  { exists (ds1 ++ [Plus; Minus; Plus] ++ ds2).
    exact (pmp_whole_embed _ _ _ _ _ Hprepared). }
  assert (Hspec : @PMPClassificationSpec old_l sub old_r
                   (classify_pmp old_l sub old_r)).
  { apply classify_pmp_spec; [|exact Hembed].
    intros p [seed [Hseed Hpath]] Hon.
    exact (classify_pmp_sources_safe old_l sub old_r
             (pmp_sub_embed _ _ _ _ _ Hprepared)
             (pmp_whole_sparse _ _ _ _ _ Hprepared) Hembed
             (pmp_extensions_disjoint _ _ _ _ _ Hprepared)
             (pmp_no_terminal_lid _ _ _ _ _ Hprepared)
             seed p Hseed Hon Hpath). }
  pose proof (pmp_replacement_slope _ _ _ _ _ Hprepared) as Hslope.
  pose proof (embedding_listDir_length_consis _ _
                (pmp_sub_embed _ _ _ _ _ Hprepared)) as Hlen.
  destruct sub as [|seg1 [|seg2 [|seg3 rest]]]; simpl in Hlen; try discriminate.
  destruct rest; simpl in Hlen; [|discriminate].
  destruct (embed_sparsely_PMP_prepared_from_spec classify_pmp
              ds1 ds2 old_l [seg1; seg2; seg3] old_r Hprepared Hspec)
    as [l [r [Hl [Hsub [Hr [Hwhole [Hsparse [Hopen Haround]]]]]]]].
  exists l, r, seg1, seg2, seg3.
  split; [exact Hslope |].
  split; [exact Hl |]. split; [exact Hsub |]. split; [exact Hr |].
  split; [exact Hwhole |]. split; [exact Hsparse |].
  split; assumption.
Qed.

(* embed_sparsely_listDir_PMP の Minus 側の三角形を使う対称版。 *)
Lemma embed_sparsely_listDir_MPM (ds1 ds2 : list Direction) :
	AdmissibleDirs (ds1 ++ [Minus; Plus; Minus] ++ ds2)
	-> exists l r seg1 seg2 seg3,
		reconnect_slope (init seg1) (term seg3) Minus
			(slope_init seg1) (slope_term seg3) (* 将来的にこの部分を，傾きを保存したまま１つのセグメントに変更できるように *)
		/\ embed_listDir ds1 l
		/\ embed_listDir [Minus; Plus; Minus] [seg1; seg2; seg3]
		/\ embed_listDir ds2 r
		/\ embed_listDir (ds1 ++ [Minus; Plus; Minus] ++ ds2) (l ++ [seg1; seg2; seg3] ++ r)
		/\ sparse_embedding (l ++ [seg1; seg2; seg3] ++ r)
		/\ ~ close (l ++ [seg1; seg2; seg3] ++ r)
		/\ sparse_around_triangle Minus l [seg1; seg2; seg3] r.
Proof. Admitted.

(* 端点長方形内の PPMM は、両端の傾きを保つ PM の接続点を取れる。
   割線傾きと端点傾きの関係、および指定傾きのセグメントの存在が必要。 *)
Lemma ppmm_inside_rect_has_pm_slopes :
  forall s1 s2 s3 s4,
    embed_listDir [Plus; Plus; Minus; Minus] [s1; s2; s3; s4] ->
    sub_strictly_inside_endpoint_rect [s1; s2; s3; s4] ->
    fst (init s1) < fst (term s4) ->
    reconnect_slope_pair (init s1) (term s4) Plus Minus
      (slope_init s1) (slope_term s4).
Admitted.

(* PPMM は全域で三角形疎、簡約部分の周りでは閉長方形で疎。 *)
Lemma embed_sparsely_listDir_PPMM (ds1 ds2 : list Direction) :
	AdmissibleDirs (ds1 ++ [Plus; Plus; Minus; Minus] ++ ds2)
	-> exists l r seg1 seg2 seg3 seg4, 
		reconnect_slope_pair (init seg1) (term seg4) Plus Minus
			(slope_init seg1) (slope_term seg4) (* 将来的にこの部分を，傾きを保存したまま２つのセグメントに変更できるように *)
		/\ embed_listDir ds1 l
		/\ embed_listDir [Plus; Plus; Minus; Minus] [seg1; seg2; seg3; seg4]
		/\ embed_listDir ds2 r
		/\ embed_listDir (ds1 ++ [Plus; Plus; Minus; Minus] ++ ds2) (l ++ [seg1; seg2; seg3; seg4] ++ r)
		/\ sparse_embedding (l ++ [seg1; seg2; seg3; seg4] ++ r)
		/\ ~ close (l ++ [seg1; seg2; seg3; seg4] ++ r)
		/\ sparse_around l [seg1; seg2; seg3; seg4] r
		/\ sub_contained_in_endpoint_rect [seg1; seg2; seg3; seg4].
Proof.
  intro Hadm.
  destruct (AdmissibleDirs_has_prepared_PPMM ds1 ds2 Hadm)
    as [old_l [sub [old_r Hprepared]]].
  pose proof
    (@prepared_geometry ds1 [Plus; Plus; Minus; Minus] ds2
       old_l sub old_r Hprepared) as Hgeometry.
  pose proof (prepared_sub_strictly_inside old_l sub old_r Hgeometry)
    as Hinside.
  pose proof (prepared_sub_x_order old_l sub old_r Hgeometry) as Hx.
  pose proof (prepared_sub_contained old_l sub old_r Hgeometry) as Hcontained.
  destruct (embed_sparsely_if_both_lids_removable
              ds1 [Plus; Plus; Minus; Minus] ds2
              old_l sub old_r Hprepared)
    as [l [r [Hl [Hsub [Hr [Hwhole [Hsparse [Hopen Haround]]]]]]]].
  pose proof (embedding_listDir_length_consis _ _ Hsub) as Hlen.
  destruct sub as [|seg1 [|seg2 [|seg3 [|seg4 [|seg5 rest]]]]];
    simpl in Hlen; try lia.
  exists l, r, seg1, seg2, seg3, seg4.
  assert (Hslope :
      reconnect_slope_pair (init seg1) (term seg4) Plus Minus
        (slope_init seg1) (slope_term seg4)).
  { eapply ppmm_inside_rect_has_pm_slopes; eauto. }
  split; [exact Hslope |].
  split; [exact Hl |].
  split; [exact Hsub |].
  split; [exact Hr |].
  split; [exact Hwhole |].
  split; [exact Hsparse |].
  split; [exact Hopen |]. split; [exact Haround | exact Hcontained].
Qed.

(* 端点長方形内の MMPP についての対称な傾き接続補題。 *)
Lemma mmpp_inside_rect_has_mp_slopes :
  forall s1 s2 s3 s4,
    embed_listDir [Minus; Minus; Plus; Plus] [s1; s2; s3; s4] ->
    sub_strictly_inside_endpoint_rect [s1; s2; s3; s4] ->
    fst (init s1) < fst (term s4) ->
    reconnect_slope_pair (init s1) (term s4) Minus Plus
      (slope_init s1) (slope_term s4).
Admitted.

(* embed_sparsely_listDir_PPMM の Minus 版． *)
Lemma embed_sparsely_listDir_MMPP (ds1 ds2 : list Direction) :
	AdmissibleDirs (ds1 ++ [Minus; Minus; Plus; Plus] ++ ds2)
	-> exists l r seg1 seg2 seg3 seg4,
		reconnect_slope_pair (init seg1) (term seg4) Minus Plus
			(slope_init seg1) (slope_term seg4) (* 将来的にこの部分を，傾きを保存したまま２つのセグメントに変更できるように *)
		/\ embed_listDir ds1 l
		/\ embed_listDir [Minus; Minus; Plus; Plus] [seg1; seg2; seg3; seg4]
		/\ embed_listDir ds2 r
		/\ embed_listDir (ds1 ++ [Minus; Minus; Plus; Plus] ++ ds2) (l ++ [seg1; seg2; seg3; seg4] ++ r)
		/\ sparse_embedding (l ++ [seg1; seg2; seg3; seg4] ++ r)
		/\ ~ close (l ++ [seg1; seg2; seg3; seg4] ++ r)
		/\ sparse_around l [seg1; seg2; seg3; seg4] r
		/\ sub_contained_in_endpoint_rect [seg1; seg2; seg3; seg4].
Proof.
  intro Hadm.
  destruct (AdmissibleDirs_has_prepared_MMPP ds1 ds2 Hadm)
    as [old_l [sub [old_r Hprepared]]].
  pose proof
    (@prepared_geometry ds1 [Minus; Minus; Plus; Plus] ds2
       old_l sub old_r Hprepared) as Hgeometry.
  pose proof (prepared_sub_strictly_inside old_l sub old_r Hgeometry)
    as Hinside.
  pose proof (prepared_sub_x_order old_l sub old_r Hgeometry) as Hx.
  pose proof (prepared_sub_contained old_l sub old_r Hgeometry) as Hcontained.
  destruct (embed_sparsely_if_both_lids_removable
              ds1 [Minus; Minus; Plus; Plus] ds2
              old_l sub old_r Hprepared)
    as [l [r [Hl [Hsub [Hr [Hwhole [Hsparse [Hopen Haround]]]]]]]].
  pose proof (embedding_listDir_length_consis _ _ Hsub) as Hlen.
  destruct sub as [|seg1 [|seg2 [|seg3 [|seg4 [|seg5 rest]]]]];
    simpl in Hlen; try lia.
  exists l, r, seg1, seg2, seg3, seg4.
  assert (Hslope :
      reconnect_slope_pair (init seg1) (term seg4) Minus Plus
        (slope_init seg1) (slope_term seg4)).
  { eapply mmpp_inside_rect_has_mp_slopes; eauto. }
  split; [exact Hslope |].
  split; [exact Hl |].
  split; [exact Hsub |].
  split; [exact Hr |].
  split; [exact Hwhole |].
  split; [exact Hsparse |].
  split; [exact Hopen |]. split; [exact Haround | exact Hcontained].
Qed.

(* Plus セグメントを、元の閉端点三角形内で、端点と端点傾きを保って
   [Plus; Minus; Plus] に分割する。開性の保存は別補題で扱う。 *)
Lemma embedding_P_to_PMP_in_triangle : forall (seg : Segment),
	embed_listDir [Plus] [seg]
	-> exists seg1 seg2 seg3,
		embed_listDir [Plus; Minus; Plus] [seg1; seg2; seg3]
		/\ in_segment_triangle_of seg [seg1; seg2; seg3]
		/\ same_init_and_term [seg] [seg1; seg2; seg3]
		/\ same_slope_init_and_term [seg] [seg1; seg2; seg3].
Proof. 
	(* 三角形の境界上にある旧セグメントも含め、交互の凸性を持つ
	   置換を三角形内で構成する必要がある。 *)
Admitted.

(* embedding_P_to_PMP_in_triangle の Minus 版。 *)
Lemma embedding_M_to_MPM_in_triangle : forall (seg : Segment),
	embed_listDir [Minus] [seg]
	-> exists seg1 seg2 seg3,
		embed_listDir [Minus; Plus; Minus] [seg1; seg2; seg3]
		/\ in_segment_triangle_of seg [seg1; seg2; seg3]
		/\ same_init_and_term [seg] [seg1; seg2; seg3]
		/\ same_slope_init_and_term [seg] [seg1; seg2; seg3].
Proof. Admitted.

(* [Plus; Minus] の埋め込みを，端点とそこでの傾きを保存したまま
		[Plus; Plus; Minus; Minus] の埋め込みとなる4つに矩形内で分割できる *)
Lemma embedding_PM_to_PPMM_in_rect : forall (seg1 seg2 : Segment),
	embed_listDir [Plus; Minus] [seg1; seg2]
	-> exists seg1' seg2' seg3' seg4',
		embed_listDir [Plus; Plus; Minus; Minus] [seg1'; seg2'; seg3'; seg4'] (* この内部で seg1-3 が連結していることは示されてほしい *)
		/\ in_rect_or_endpoints [seg1; seg2] [seg1'; seg2'; seg3'; seg4'] (* seg が張る矩形の内部で分割できている *)
		/\ same_init_and_term [seg1; seg2] [seg1'; seg2'; seg3'; seg4']
		/\ same_slope_init_and_term [seg1; seg2] [seg1'; seg2'; seg3'; seg4'].
Proof. Admitted.

(* embedding_PM_to_PPMM_in_rect の Minus 版 *)
Lemma embedding_MP_to_MMPP_in_rect : forall (seg1 seg2 : Segment),
	embed_listDir [Minus; Plus] [seg1; seg2]
	-> exists seg1' seg2' seg3' seg4',
		embed_listDir [Minus; Minus; Plus; Plus] [seg1'; seg2'; seg3'; seg4']
		/\ in_rect_or_endpoints [seg1; seg2] [seg1'; seg2'; seg3'; seg4']
		/\ same_init_and_term [seg1; seg2] [seg1'; seg2'; seg3'; seg4']
		/\ same_slope_init_and_term [seg1; seg2] [seg1'; seg2'; seg3'; seg4'].
Proof. Admitted.

(* 両端で指定された傾きを実現できるなら，PMP の埋め込みを，端点と傾きを
		保存したまま、その端点が定める Plus 側の三角形内に変更できる． *)
(* TODO : もう少し一般化しても良いかもしれない *)
Lemma embedding_PMP_to_P_in_triangle : forall (seg1 seg2 seg3 : Segment),
	reconnect_slope (init seg1) (term seg3) Plus
		(slope_init seg1) (slope_term seg3)
	-> embed_listDir [Plus; Minus; Plus] [seg1; seg2; seg3]
	->
	exists seg,
		embed_listDir [Plus] [seg]
		/\ in_sub_triangle_of Plus [seg1; seg2; seg3] [seg]
		/\ same_init_and_term [seg1; seg2; seg3] [seg]
		/\ same_slope_init_and_term [seg1; seg2; seg3] [seg].
Proof.
	(* reconnect_slope_* が保証する両端の条件を同時に満たす Plus の埋め込みを取る． *)
Admitted.

(* embedding_PMP_to_P_in_triangle の Minus 版． *)
Lemma embedding_MPM_to_M_in_triangle : forall (seg1 seg2 seg3 : Segment),
	reconnect_slope (init seg1) (term seg3) Minus
		(slope_init seg1) (slope_term seg3)
	-> embed_listDir [Minus; Plus; Minus] [seg1; seg2; seg3]
	->
	exists seg,
		embed_listDir [Minus] [seg]
		/\ in_sub_triangle_of Minus [seg1; seg2; seg3] [seg]
		/\ same_init_and_term [seg1; seg2; seg3] [seg]
		/\ same_slope_init_and_term [seg1; seg2; seg3] [seg].
Proof. Admitted.

(* PP と MM の各部分について両端点・両端傾きを同時に実現できるなら，
		それらを矩形内の Plus，Minus セグメントへそれぞれ縮約できる． *)
Lemma embedding_PPMM_to_PM_in_rect : forall (seg1 seg2 seg3 seg4 : Segment),
	reconnect_slope_pair (init seg1) (term seg4) Plus Minus
		(slope_init seg1) (slope_term seg4)
	-> embed_listDir [Plus; Plus; Minus; Minus] [seg1; seg2; seg3; seg4]
	->
	exists seg1' seg2',
		embed_listDir [Plus; Minus] [seg1'; seg2'] 
		/\ in_rect_or_endpoints [seg1; seg2; seg3; seg4] [seg1'; seg2'] (* seg が張る矩形の内部で分割できている *)
		/\ same_init_and_term [seg1; seg2; seg3; seg4] [seg1'; seg2']
		/\ same_slope_init_and_term [seg1; seg2; seg3; seg4] [seg1'; seg2'].
Proof.
	(* 始点から中心へ，終点から中心へそれぞれ Plus, Minus の埋め込みをとり，繋げれば良さそう *)
Admitted.

(* embedding_PPMM_to_PM_in_rect の Minus 版． *)
Lemma embedding_MMPP_to_MP_in_rect : forall (seg1 seg2 seg3 seg4 : Segment),
	reconnect_slope_pair (init seg1) (term seg4) Minus Plus
		(slope_init seg1) (slope_term seg4)
	-> embed_listDir [Minus; Minus; Plus; Plus] [seg1; seg2; seg3; seg4]
	->
	exists seg1' seg2',
		embed_listDir [Minus; Plus] [seg1'; seg2']
		/\ in_rect_or_endpoints [seg1; seg2; seg3; seg4] [seg1'; seg2']
		/\ same_init_and_term [seg1; seg2; seg3; seg4] [seg1'; seg2']
		/\ same_slope_init_and_term [seg1; seg2; seg3; seg4] [seg1'; seg2'].
Proof. Admitted.

(* 埋め込みの scurve 証人は、具体的セグメントの primitive 列と一致する。 *)
Lemma embedded_primitive_list : forall sc ls,
  embed_scurve sc ls -> proj1_sig sc = map primitive_segment ls.
Proof.
  intros sc ls Hembed. induction Hembed; simpl; try reflexivity.
  - assert (Hps : ps = primitive_segment s) by
      (eapply embed_unique; eauto using primitive_segment_embed).
    now rewrite Hps.
  - assert (Hps1 : ps = primitive_segment s1) by
      (eapply embed_unique; eauto using primitive_segment_embed).
    now rewrite Hps1, IHHembed.
Qed.

Lemma embedded_direction_list : forall ds ls,
  embed_listDir ds ls -> ds = map orn_seg ls.
Proof.
  intros ds ls [sc [Hdir Hembed]].
  rewrite <- Hdir. unfold scurve_to_direction.
  rewrite (embedded_primitive_list sc ls Hembed), map_map.
  apply map_ext. intros t. symmetry. apply orn_seg_primitive.
Qed.

(* Plus/Minus を切り替える接続では、南北・東西の進行方向は変わらない。 *)
Lemma dc_opposite_axes : forall p q,
  dc p q -> orn p <> orn q ->
  V_of p = V_of q /\ H_of p = H_of q.
Proof.
  intros p q Hdc Hdiff. destruct Hdc;
    unfold V_of, H_of; simpl; try tauto;
    destruct h; simpl in Hdiff; contradiction.
Qed.

Lemma alternating_embedding_axes : forall sc ls,
  embed_scurve sc ls ->
  (forall i a b, nth_error ls i = Some a ->
     nth_error ls (S i) = Some b -> orn_seg a <> orn_seg b) ->
  forall t, In t ls ->
    V_of (primitive_segment t) = V_of (primitive_segment (hd_segment ls))
    /\ H_of (primitive_segment t) = H_of (primitive_segment (hd_segment ls)).
Proof.
  intros sc ls Hembed. induction Hembed as
    [|ps a Ha|ps tail A a b rest Ha Htail IH Hjoin]; intros Halt t Hin.
  - contradiction.
  - destruct Hin as [-> | []]. auto.
  - destruct Hin as [-> | Hin]; [auto |].
    assert (HtailAlt : forall i u v,
      nth_error (b :: rest) i = Some u ->
      nth_error (b :: rest) (S i) = Some v -> orn_seg u <> orn_seg v).
    { intros i u v Hu Hv. exact (Halt (S i) u v Hu Hv). }
    specialize (IH HtailAlt t Hin).
    destruct (embed_scurve_adjacent_data _ _ 0 a b
      (EmbedScurveCons ps tail A a b rest Ha Htail Hjoin)
      eq_refl eq_refl) as [pa [pb [Hpa [Hpb [Hdc _]]]]].
    assert (Ea : pa = primitive_segment a) by
      (eapply embed_unique; eauto using primitive_segment_embed).
    assert (Eb : pb = primitive_segment b) by
      (eapply embed_unique; eauto using primitive_segment_embed).
    rewrite Ea, Eb in Hdc.
    destruct (dc_opposite_axes _ _ Hdc ltac:(
      rewrite <- !orn_seg_primitive; exact (Halt 0%nat a b eq_refl eq_refl)))
      as [Hv Hh].
    change (V_of (primitive_segment t) = V_of (primitive_segment b)
      /\ H_of (primitive_segment t) = H_of (primitive_segment b)) in IH.
    change (V_of (primitive_segment t) = V_of (primitive_segment a)
      /\ H_of (primitive_segment t) = H_of (primitive_segment a)).
    destruct IH as [IV IH].
    split; congruence.
Qed.

(* 同じ南北・東西方向の連結列は、列全体の端点長方形内にある。 *)
Lemma connected_fixed_axes_bounds : forall ls v h,
  connected ls ->
  (forall t, In t ls -> exists c, embed (v, h, c) t) ->
  forall p, onSegmentlist ls p ->
    horizontal_order h (fst (init (hd_segment ls))) (fst p)
    /\ horizontal_order h (fst p) (fst (term (last_segment ls)))
    /\ vertical_order v (snd (init (hd_segment ls))) (snd p)
    /\ vertical_order v (snd p) (snd (term (last_segment ls))).
Proof.
  induction ls as [|a tail IH]; intros v h Hconn Haxes p [t [Hin Hon]];
    [contradiction |].
  destruct (Haxes a ltac:(now left)) as [ca Ha].
  destruct tail as [|b rest].
  - destruct Hin as [<- | []]. cbn [hd_segment last_segment].
    destruct p as [x y], v, h;
      cbn [horizontal_order vertical_order];
      first [pose proof (e_onseg_relation a _ _ x y Ha Hon)
            |pose proof (w_onseg_relation a _ _ x y Ha Hon)];
      first [pose proof (n_onseg_relation a _ _ x y Ha Hon)
            |pose proof (s_onseg_relation a _ _ x y Ha Hon)]; tauto.
  - assert (HtailConn : connected (b :: rest)).
    { intros i u z Hu Hz. exact (Hconn (S i) u z Hu Hz). }
    assert (HtailAxes : forall t, In t (b :: rest) -> exists c, embed (v,h,c) t).
    { intros z Hz. apply Haxes. now right. }
    pose proof (Hconn 0%nat a b eq_refl eq_refl) as Hjoin.
    pose proof (IH v h HtailConn HtailAxes (init b)
      ltac:(exists b; split; [now left | apply onInit])) as Hend.
    change (horizontal_order h (fst (init b)) (fst (init b))
      /\ horizontal_order h (fst (init b)) (fst (term (last_segment (b :: rest))))
      /\ vertical_order v (snd (init b)) (snd (init b))
      /\ vertical_order v (snd (init b)) (snd (term (last_segment (b :: rest))))) in Hend.
    change (horizontal_order h (fst (init a)) (fst p)
      /\ horizontal_order h (fst p) (fst (term (last_segment (b :: rest))))
      /\ vertical_order v (snd (init a)) (snd p)
      /\ vertical_order v (snd p) (snd (term (last_segment (b :: rest))))).
    destruct Hin as [<- | Hin].
    + destruct p as [x y], v, h;
        cbn [horizontal_order vertical_order] in Hend |- *;
        first [pose proof (e_onseg_relation a _ _ x y Ha Hon)
              |pose proof (w_onseg_relation a _ _ x y Ha Hon)];
        first [pose proof (n_onseg_relation a _ _ x y Ha Hon)
              |pose proof (s_onseg_relation a _ _ x y Ha Hon)];
        rewrite <- Hjoin in Hend; simpl in *; lra.
    + pose proof (IH v h HtailConn HtailAxes p
        ltac:(exists t; now split)) as Hp.
      change (horizontal_order h (fst (init b)) (fst p)
        /\ horizontal_order h (fst p) (fst (term (last_segment (b :: rest))))
        /\ vertical_order v (snd (init b)) (snd p)
        /\ vertical_order v (snd p) (snd (term (last_segment (b :: rest))))) in Hp.
      destruct v, h; cbn [horizontal_order vertical_order] in Hp |- *;
        first [pose proof (e_end_relation a _ _ Ha)
              |pose proof (w_end_relation a _ _ Ha)];
        first [pose proof (n_end_relation a _ _ Ha)
              |pose proof (s_end_relation a _ _ Ha)];
        rewrite Hjoin in *; simpl in *; lra.
Qed.

Lemma alternating_embedding_contained : forall ds ls,
  embed_listDir ds ls ->
  (forall i d d', nth_error ds i = Some d ->
    nth_error ds (S i) = Some d' -> d <> d') ->
  sub_contained_in_endpoint_rect ls.
Proof.
  intros ds ls Hembed Halt.
  pose proof (embedded_direction_list ds ls Hembed) as Hdirs.
  destruct Hembed as [sc [Hdir Hsc]].
  assert (HaltSeg : forall i a b, nth_error ls i = Some a ->
    nth_error ls (S i) = Some b -> orn_seg a <> orn_seg b).
  { intros i a b Ha Hb. apply (Halt i); rewrite Hdirs, nth_error_map;
      [rewrite Ha | rewrite Hb]; reflexivity. }
  pose proof (alternating_embedding_axes sc ls Hsc HaltSeg) as Haxes.
  destruct (primitive_segment (hd_segment ls)) as [[v h] c] eqn:E.
  assert (HembedAxes : forall t, In t ls -> exists c, embed (v,h,c) t).
  { intros t Ht. destruct (Haxes t Ht) as [Hv Hh].
    destruct (primitive_segment t) as [[vt ht] ct] eqn:Et.
    rewrite ?E, ?Et in Hv, Hh. cbv [V_of H_of fst snd] in Hv, Hh. subst vt ht.
    exists ct. rewrite <- Et. apply primitive_segment_embed. }
  intros p Hp.
  pose proof (connected_fixed_axes_bounds ls v h
    (embed_scurve_connected sc ls Hsc) HembedAxes p Hp) as Hbounds.
  unfold in_rect_or_endpoints_at, in_closed_rect, rect_of; simpl.
  destruct v, h; cbn [horizontal_order vertical_order] in Hbounds;
    unfold Rmin, Rmax; repeat destruct Rle_dec; lra.
Qed.

(* 同じ端点長方形に収まる置換で、両端の Plus/Minus が同じなら primitive も保存される。 *)
Lemma contained_replacement_boundary_primitives : forall ds ds' old new,
  old <> [] -> new <> [] ->
  embed_listDir ds old -> embed_listDir ds' new ->
  hd Plus ds = hd Plus ds' -> last ds Plus = last ds' Plus ->
  sub_contained_in_endpoint_rect old ->
  in_rect_or_endpoints old new ->
  same_init_and_term old new ->
  primitive_segment (hd_segment new) = primitive_segment (hd_segment old)
  /\ primitive_segment (last_segment new) = primitive_segment (last_segment old).
Proof.
  intros ds ds' old new Hold Hnew HembedOld HembedNew Hhd Hlast
    Hcontained Hinside [Hi Ht].
  pose proof (embedded_direction_list ds old HembedOld) as Eold.
  pose proof (embedded_direction_list ds' new HembedNew) as Enew.
  assert (HornHead : orn_seg (hd_segment new) = orn_seg (hd_segment old)).
  { rewrite Eold, Enew in Hhd. destruct old, new; try contradiction.
    simpl in Hhd. now symmetry. }
  assert (HornLast : orn_seg (last_segment new) = orn_seg (last_segment old)).
  { assert (HmapLast : forall ts, ts <> [] ->
      last (map orn_seg ts) Plus = orn_seg (last_segment ts)).
    { intros [|a ts] Hts; [contradiction |].
      unfold last_segment. clear Hts. revert a.
      induction ts as [|b ts IH]; intros a; simpl; [reflexivity | exact (IH b)]. }
    rewrite Eold, Enew, (HmapLast old Hold), (HmapLast new Hnew) in Hlast.
    exact (eq_sym Hlast). }
  pose proof (Hcontained _ ltac:(exists (hd_segment old); split;
    [destruct old; [contradiction | now left] | apply onTerm])) as Hoh.
  pose proof (Hcontained _ ltac:(exists (last_segment old); split;
    [apply last_In; exact Hold | apply onInit])) as Hol.
  pose proof (Hinside _ ltac:(exists (hd_segment new); split;
    [destruct new; [contradiction | now left] | apply onTerm])) as Hnh.
  pose proof (Hinside _ ltac:(exists (last_segment new); split;
    [apply last_In; exact Hnew | apply onInit])) as Hnl.
  unfold in_rect_or_endpoints_at, in_closed_rect, rect_of in Hoh, Hol, Hnh, Hnl;
    simpl in Hoh, Hol, Hnh, Hnl.
  pose proof (neq_init_term_x (hd_segment old)) as Hoxh.
  pose proof (neq_init_term_y (hd_segment old)) as Hoyh.
  pose proof (neq_init_term_x (last_segment old)) as Hoxl.
  pose proof (neq_init_term_y (last_segment old)) as Hoyl.
  pose proof (neq_init_term_x (hd_segment new)) as Hnxh.
  pose proof (neq_init_term_y (hd_segment new)) as Hnyh.
  pose proof (neq_init_term_x (last_segment new)) as Hnxl.
  pose proof (neq_init_term_y (last_segment new)) as Hnyl.
  unfold init_x, term_x, init_y, term_y in *.
  rewrite <- Hi in Hnxh, Hnyh. rewrite <- Ht in Hnxl, Hnyl.
  unfold Rmin, Rmax in Hoh, Hol, Hnh, Hnl.
  split; apply same_primitive_of_axis_orders; try assumption;
    rewrite <- ?Hi, <- ?Ht; repeat destruct Rle_dec; split; intro; lra.
Qed.

Lemma primitive_map_last : forall ls,
  ls <> [] -> last (map primitive_segment ls) default_primitive_segment =
    primitive_segment (last_segment ls).
Proof.
  intros [|a ls] H; [contradiction |]. clear H. unfold last_segment. revert a.
  induction ls as [|b ls IH]; intros a; simpl; [reflexivity | exact (IH b)].
Qed.

Lemma scurve_app_suffix : forall ps qs,
  is_scurve (ps ++ qs) -> is_scurve qs.
Proof.
  induction ps as [|p ps IH]; intros qs H; [exact H |].
  apply IH. now apply is_scurve_tail in H.
Qed.

Lemma scurve_app_last_connection : forall ps qs,
  ps <> [] -> is_scurve (ps ++ qs) ->
  dc_pseg_hd (last ps default_primitive_segment) qs.
Proof.
  induction ps as [|p ps IH]; intros qs Hne Hcurve; [contradiction |].
  destruct ps as [|q ps].
  - simpl in *. inversion Hcurve; assumption.
  - change (dc_pseg_hd (last (q :: ps) default_primitive_segment) qs).
    apply IH; [discriminate |]. now apply is_scurve_tail in Hcurve.
Qed.

(* 境界の接続証明だけを用いて、二つの scurve の primitive 列を連結する。 *)
Lemma scurve_app_join : forall ps qs,
  is_scurve ps -> is_scurve qs ->
  (ps <> [] -> dc_pseg_hd (last ps default_primitive_segment) qs) ->
  is_scurve (ps ++ qs).
Proof.
  induction ps as [|p ps IH]; intros qs Hps Hqs Hjoin; [exact Hqs |].
  destruct ps as [|q ps].
  - simpl. constructor; [exact Hqs |]. apply Hjoin. discriminate.
  - simpl. constructor.
    + apply IH; [now apply is_scurve_tail in Hps | exact Hqs |].
      intros _. exact (Hjoin ltac:(discriminate)).
    + eapply dc_pseg_hd_hd_error with (l1 := q :: ps); [reflexivity |].
      inversion Hps; assumption.
Qed.

Lemma scurve_replace_primitive_middle : forall prefix old new suffix,
  old <> [] -> new <> [] ->
  is_scurve (prefix ++ old ++ suffix) -> is_scurve new ->
  hd default_primitive_segment old = hd default_primitive_segment new ->
  last old default_primitive_segment = last new default_primitive_segment ->
  is_scurve (prefix ++ new ++ suffix).
Proof.
  induction prefix as [|p prefix IH]; intros old new suffix Hold Hnew
    Hcurve Hmiddle Hhead Hlast.
  - simpl in *. apply scurve_app_join; [exact Hmiddle | |].
    + eapply scurve_app_suffix. exact Hcurve.
    + intros _. rewrite <- Hlast.
      now apply scurve_app_last_connection with (ps := old).
  - simpl in *. constructor.
    + apply (IH old new suffix Hold Hnew); try assumption.
      now apply is_scurve_tail in Hcurve.
    + eapply dc_pseg_hd_hd_error with (l1 := prefix ++ old ++ suffix).
      * destruct prefix as [|q prefix]; [|reflexivity].
        destruct old, new; try contradiction. simpl in Hhead |- *. now rewrite Hhead.
      * inversion Hcurve; assumption.
Qed.

Lemma connected_join : forall l r,
  connected l -> connected r ->
  (l <> [] -> r <> [] -> term (last_segment l) = init (hd_segment r)) ->
  connected (l ++ r).
Proof.
  induction l as [|a l IH]; intros r Hl Hr Hjoin; [exact Hr |].
  destruct l as [|b l].
  - intros [|i] u v Hu Hv.
    + simpl in Hu. injection Hu as <-. destruct r as [|b r]; [discriminate |].
      simpl in Hv. injection Hv as <-.
      exact (Hjoin ltac:(discriminate) ltac:(discriminate)).
    + exact (Hr i u v Hu Hv).
  - assert (Htail : connected ((b :: l) ++ r)).
    { apply IH; [|exact Hr |].
      - intros i u v Hu Hv. exact (Hl (S i) u v Hu Hv).
      - intros _ Hrn. exact (Hjoin ltac:(discriminate) Hrn). }
    intros [|i] u v Hu Hv.
    + simpl in Hu, Hv. injection Hu as <-. injection Hv as <-.
      exact (Hl 0%nat a b eq_refl eq_refl).
    + exact (Htail i u v Hu Hv).
Qed.

(* 各セグメントの primitive と連結性から、scurve 内の dc 証明を再利用して埋め込む。 *)
Lemma embed_connected_primitive_list : forall ls sc,
  proj1_sig sc = map primitive_segment ls -> connected ls -> embed_scurve sc ls.
Proof.
  induction ls as [|a ls IH]; intros sc E Hconn.
  - replace sc with nil_scurve by (apply scurve_ext; exact (eq_sym E)).
    constructor.
  - destruct ls as [|b ls].
    + replace sc with (connect (primitive_segment a) nil_scurve (DcNil (primitive_segment a))) by
        (apply scurve_ext; exact (eq_sym E)).
      apply EmbedScurveSigle. apply primitive_segment_embed.
    + assert (Hvalid : is_scurve (map primitive_segment (a :: b :: ls))).
      { rewrite <- E. exact (proj2_sig sc). }
      assert (Htail : is_scurve (map primitive_segment (b :: ls))).
      { now apply is_scurve_tail in Hvalid. }
      assert (A : dc_pseg_hd (primitive_segment a) (map primitive_segment (b :: ls))).
      { inversion Hvalid; assumption. }
      replace sc with (connect (primitive_segment a)
        (exist _ (map primitive_segment (b :: ls)) Htail) A) by
          (apply scurve_ext; exact (eq_sym E)).
      eapply EmbedScurveCons with (A := A).
      * apply primitive_segment_embed.
      * apply IH; [reflexivity |].
        intros i u v Hu Hv. exact (Hconn (S i) u v Hu Hv).
      * exact (Hconn 0%nat a b eq_refl eq_refl).
Qed.

(* 左右を変えず、端点と両端 primitive を保存して中央の埋め込みを置換する。
   結論の左右の方向列は、実際のセグメント列から読み取る。 *)
Lemma embedding_inner_change : forall ds ds' l sub r sub',
  embed_listDir ds (l ++ sub ++ r) ->
  embed_listDir ds' sub' ->
  sub <> [] -> sub' <> [] ->
  same_init_and_term sub sub' ->
  primitive_segment (hd_segment sub') = primitive_segment (hd_segment sub) ->
  primitive_segment (last_segment sub') = primitive_segment (last_segment sub) ->
  embed_listDir (map orn_seg l ++ ds' ++ map orn_seg r) (l ++ sub' ++ r).
Proof.
  intros ds ds' l sub r sub' [sc1 [_ Hembed]] Hembed_dir2 Hsub Hsub'
    Hinit_term HprimitiveHead HprimitiveLast.
  pose proof (embedded_primitive_list sc1 _ Hembed) as Eold.
  assert (HvalidOld : is_scurve (map primitive_segment (l ++ sub ++ r))).
  { rewrite <- Eold. exact (proj2_sig sc1). }
  destruct Hembed_dir2 as [middle [HmiddleDir HmiddleEmbed]].
  assert (HvalidMiddle : is_scurve (map primitive_segment sub')).
  { rewrite <- (embedded_primitive_list middle sub' HmiddleEmbed).
    exact (proj2_sig middle). }
  assert (HvalidNew : is_scurve (map primitive_segment (l ++ sub' ++ r))).
  { rewrite !map_app. apply scurve_replace_primitive_middle with (old := map primitive_segment sub).
    - intro E. apply Hsub. now apply map_eq_nil in E.
    - intro E. apply Hsub'. now apply map_eq_nil in E.
    - now rewrite <- !map_app.
    - exact HvalidMiddle.
    - destruct sub, sub'; try contradiction. exact (eq_sym HprimitiveHead).
    - rewrite (primitive_map_last sub Hsub), (primitive_map_last sub' Hsub').
      exact (eq_sym HprimitiveLast). }
  pose proof (embed_scurve_connected sc1 _ Hembed) as HconnOld.
  destruct Hinit_term as [Hi Ht].
  assert (HconnRight : connected r).
  { eapply connected_middle with (l := l ++ sub) (r := []).
    now rewrite app_nil_r, <- app_assoc. }
  assert (HconnOldTail : connected (sub ++ r)).
  { eapply connected_middle with (l := l) (r := []). now rewrite app_nil_r. }
  assert (HconnNewTail : connected (sub' ++ r)).
  { apply connected_join; [exact (embed_scurve_connected middle sub' HmiddleEmbed) | exact HconnRight |].
    intros _ Hr. rewrite <- Ht.
    exact (connected_app_junction sub r HconnOldTail Hsub Hr). }
  assert (HconnNew : connected (l ++ sub' ++ r)).
  { apply connected_join; [|exact HconnNewTail |].
    - eapply connected_middle with (l := []) (r := sub ++ r). exact HconnOld.
    - intros Hl _.
      pose proof (connected_app_junction l (sub ++ r) HconnOld Hl
        ltac:(destruct sub; [contradiction | discriminate])) as Hj.
      destruct sub, sub'; try contradiction. exact (eq_trans Hj Hi). }
  set (actual := exist is_scurve _ HvalidNew).
  assert (Hactual : embed_scurve actual (l ++ sub' ++ r)).
  { apply embed_connected_primitive_list; [reflexivity | exact HconnNew]. }
  exists actual. split; [|exact Hactual].
  pose proof (embedded_direction_list (scurve_to_direction actual) _
    ltac:(exists actual; split; [reflexivity | exact Hactual])) as E.
  rewrite !map_app in E.
  rewrite <- (embedded_direction_list ds' sub'
    ltac:(exists middle; now split)) in E. exact E.
Qed.

(* 【証明の本質としている補題２】 sub_ls の周りが疎な開埋め込みにおいて，端点で傾きを保ちつつ
		sub_ls をその領域に収まる開な sub_ls' に置き換えても開のまま *)
(* TODO : もうちょっと自動化できるはず．．． *)
(* TODO : 隣接セグメントが交わらないことを使い，内部で場合分けを増やす必要がある *)
Lemma seg_in_rectangle_keep_openness : forall ds (ls rs sub_ls sub_ls' : list Segment),
	embed_listDir ds (ls ++ sub_ls ++ rs)
	-> sub_ls <> []
	-> sub_ls' <> [] 
	-> ~ close sub_ls'
	-> ~ close (ls ++ sub_ls ++ rs)
	-> sparse_around ls sub_ls rs
	-> in_rect_or_endpoints sub_ls sub_ls'
	-> same_init_and_term sub_ls sub_ls'
	-> same_slope_init_and_term sub_ls sub_ls'
	-> ~ close (ls ++ sub_ls' ++ rs).
(* strict 延長線と非隣接部分は疎性で、隣接部分は元の埋め込みの dc を用いて扱う。 *)
Admitted.

(* sub の端点三角形内の置換は開性を保つ。
   singleton の局所疎性は全域疎性から従い、複数セグメントでは別途仮定する。 *)
Lemma sub_in_triangle_keep_openness :
	forall ds d (ls rs sub replacement : list Segment),
		embed_listDir ds (ls ++ sub ++ rs)
		-> sub <> []
		-> replacement <> []
		-> ~ close replacement
		-> ~ close (ls ++ sub ++ rs)
		-> sparse_embedding (ls ++ sub ++ rs)
		-> sparse_around_triangle d ls sub rs
		-> in_sub_triangle_of d sub replacement
		-> same_init_and_term sub replacement
		-> same_slope_init_and_term sub replacement
		-> ~ close (ls ++ replacement ++ rs).
Admitted.

(* --------------------------------------------------------------------------- *)
(* 許容可能性保持に関する主張８つと，その系 *)

(* [+-+ => +] での簡約で，簡約元が許容可能なら簡約先も許容可能 *)
Lemma AdmissibleDirs_r1_Plus: forall l r,
  AdmissibleDirs (l ++ [Plus; Minus; Plus] ++ r) -> AdmissibleDirs (l ++ [Plus] ++ r).
Proof.
  intros l r admds.
  (* 疎な開埋め込みをとる *)
  pose proof (embed_sparsely_listDir_PMP _ _ admds) as H.
  destruct H as [ls1 [ls3 [seg1 [seg2 [seg3 [Hcan [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [HwholeSparse [Hopen Hsparse]]]]]]]]]]]];
  simpl in *.
  pose proof (embedding_PMP_to_P_in_triangle seg1 seg2 seg3 Hcan Hls2)
    as [segP [HP [Hin_triangle [Hinit_term Hsame_slope]]]].
  assert (HwholeEmbed :
    embed_listDir (l ++ [Plus; Minus; Plus] ++ r)
      (ls1 ++ [seg1; seg2; seg3] ++ ls3)).
  { exists sc. split; assumption. }
  assert (Hboundary :
    primitive_segment (hd_segment [segP]) = primitive_segment (hd_segment [seg1; seg2; seg3])
    /\ primitive_segment (last_segment [segP]) = primitive_segment (last_segment [seg1; seg2; seg3])).
  { eapply contained_replacement_boundary_primitives
      with (ds := [Plus; Minus; Plus]) (ds' := [Plus]).
    - discriminate.
    - discriminate.
    - exact Hls2.
    - exact HP.
    - reflexivity.
    - reflexivity.
    - eapply alternating_embedding_contained; [exact Hls2 |].
      intros [|[|[|i]]] d d' Hd Hd'; simpl in *; try discriminate;
        inversion Hd; inversion Hd'; discriminate.
    - intros p Hp. exact (proj1 (Hin_triangle p Hp)).
    - exact Hinit_term. }
  destruct Hboundary as [HprimitiveHead HprimitiveLast].
  assert (HnewWhole : embed_listDir (l ++ [Plus] ++ r)
    (ls1 ++ [segP] ++ ls3)).
  { rewrite (embedded_direction_list l ls1 Hls1),
      (embedded_direction_list r ls3 Hls3).
    eapply embedding_inner_change
      with (ds := l ++ [Plus; Minus; Plus] ++ r) (sub := [seg1; seg2; seg3]);
      try assumption; try discriminate. }
  destruct HnewWhole as [new_sc [HnewDir HnewEmbed]].
  apply AdmissibleDirs_exist. exists new_sc.
  split; [exact HnewDir |].
  exists (ls1 ++ [segP] ++ ls3).
  split; [exact HnewEmbed |].
  (* 局所置換によって開性を保存する。 *)
  apply (sub_in_triangle_keep_openness
           (l ++ [Plus; Minus; Plus] ++ r) Plus
           ls1 ls3 [seg1; seg2; seg3] [segP]);
    try assumption; try discriminate.
  apply oneway_then_open.
  apply (embedding_oneway_listDir [Plus]); try assumption.
  apply P_is_oneway.
Qed.

Lemma AdmissibleDirs_r1_Minus: forall l r,
  AdmissibleDirs (l ++ [Minus; Plus; Minus] ++ r) -> AdmissibleDirs (l ++ [Minus] ++ r).
Proof.
  intros l r admds.
  (* 疎な開埋め込みをとる *)
  pose proof (embed_sparsely_listDir_MPM _ _ admds) as H.
  destruct H as [ls1 [ls3 [seg1 [seg2 [seg3 [Hcan [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [HwholeSparse [Hopen Hsparse]]]]]]]]]]]];
  simpl in *.
  pose proof (embedding_MPM_to_M_in_triangle seg1 seg2 seg3 Hcan Hls2)
    as [segM [HM [Hin_triangle [Hinit_term Hsame_slope]]]].
  assert (HwholeEmbed :
    embed_listDir (l ++ [Minus; Plus; Minus] ++ r)
      (ls1 ++ [seg1; seg2; seg3] ++ ls3)).
  { exists sc. split; assumption. }
  assert (Hboundary :
    primitive_segment (hd_segment [segM]) = primitive_segment (hd_segment [seg1; seg2; seg3])
    /\ primitive_segment (last_segment [segM]) = primitive_segment (last_segment [seg1; seg2; seg3])).
  { eapply contained_replacement_boundary_primitives
      with (ds := [Minus; Plus; Minus]) (ds' := [Minus]).
    - discriminate.
    - discriminate.
    - exact Hls2.
    - exact HM.
    - reflexivity.
    - reflexivity.
    - eapply alternating_embedding_contained; [exact Hls2 |].
      intros [|[|[|i]]] d d' Hd Hd'; simpl in *; try discriminate;
        inversion Hd; inversion Hd'; discriminate.
    - intros p Hp. exact (proj1 (Hin_triangle p Hp)).
    - exact Hinit_term. }
  destruct Hboundary as [HprimitiveHead HprimitiveLast].
  assert (HnewWhole : embed_listDir (l ++ [Minus] ++ r)
    (ls1 ++ [segM] ++ ls3)).
  { rewrite (embedded_direction_list l ls1 Hls1),
      (embedded_direction_list r ls3 Hls3).
    eapply embedding_inner_change
      with (ds := l ++ [Minus; Plus; Minus] ++ r) (sub := [seg1; seg2; seg3]);
      try assumption; try discriminate. }
  destruct HnewWhole as [new_sc [HnewDir HnewEmbed]].
  apply AdmissibleDirs_exist. exists new_sc.
  split; [exact HnewDir |].
  exists (ls1 ++ [segM] ++ ls3).
  split; [exact HnewEmbed |].
  (* 局所置換によって開性を保存する。 *)
  apply (sub_in_triangle_keep_openness
           (l ++ [Minus; Plus; Minus] ++ r) Minus
           ls1 ls3 [seg1; seg2; seg3] [segM]);
    try assumption; try discriminate.
  apply oneway_then_open.
  apply (embedding_oneway_listDir [Minus]); try assumption.
  apply M_is_oneway.
Qed.

(* [+-+ => +] での簡約で，簡約先が許容可能ならもともと許容可能 *)
Lemma AdmissibleDirs_r1_Plus_inv: forall l r,
  AdmissibleDirs (l ++ [Plus] ++ r) -> AdmissibleDirs (l ++ [Plus; Minus; Plus] ++ r).
Proof.
  intros l r admds.
  (* 疎な開埋め込みをとる *)
  destruct (AdmissibleDirs_has_sparse_embedding _ admds)
  as [ls [Hls [HwholeSparse Hext]]].
  destruct (embed_split l [Plus] r ls Hls)
  as [ls1 [ls2 [ls3 [Heq [Hls1 [Hls2 Hls3]]]]]].
  subst ls.
  destruct (embedding_one_dir Plus ls2 Hls2) as [segP HP].
  subst ls2.
  assert (Hne : ls1 ++ [segP] ++ ls3 <> []).
  { intro Hnil. apply app_eq_nil in Hnil as [_ Htail]. discriminate Htail. }
  pose proof (sparse_extensions_open _ _ Hne Hls HwholeSparse Hext) as Hopen.
  destruct Hls as [sc [Hdir_sc Hembed]].
  simpl in *.
  assert (H: embed_listDir (l ++ [Plus] ++ r) (ls1 ++ [segP] ++ ls3)). { (* scurve ではなく向き列の方が扱いやすい *)
    unfold embed_listDir. exists sc. split; assumption.
  }
  pose proof (embedding_P_to_PMP_in_triangle segP Hls2)
    as [seg1 [seg2 [seg3 [HPMP [Hin_triangle [Hinit_term Hslope]]]]]].
  assert (HreplacementOpen : ~ close [seg1; seg2; seg3]).
  { apply oneway_then_open.
    apply (embedding_oneway_listDir [Plus; Minus; Plus]); try assumption.
    apply PMP_is_oneway. }
  assert (Hboundary :
    primitive_segment (hd_segment [seg1; seg2; seg3]) = primitive_segment (hd_segment [segP])
    /\ primitive_segment (last_segment [seg1; seg2; seg3]) = primitive_segment (last_segment [segP])).
  { eapply contained_replacement_boundary_primitives
      with (ds := [Plus]) (ds' := [Plus; Minus; Plus]).
    - discriminate.
    - discriminate.
    - exact Hls2.
    - exact HPMP.
    - reflexivity.
    - reflexivity.
    - eapply alternating_embedding_contained; [exact Hls2 |].
      intros [|[|[|i]]] d d' Hd Hd'; simpl in *; try discriminate;
        inversion Hd; inversion Hd'; discriminate.
    - intros p Hp. exact (proj1 (Hin_triangle p Hp)).
    - exact Hinit_term. }
  destruct Hboundary as [HprimitiveHead HprimitiveLast].
  assert (HnewWhole : embed_listDir (l ++ [Plus; Minus; Plus] ++ r)
    (ls1 ++ [seg1; seg2; seg3] ++ ls3)).
  { rewrite (embedded_direction_list l ls1 Hls1),
      (embedded_direction_list r ls3 Hls3).
    eapply embedding_inner_change
      with (ds := l ++ [Plus] ++ r) (sub := [segP]);
      try assumption; try discriminate. }
  destruct HnewWhole as [new_sc [HnewDir HnewEmbed]].
  apply AdmissibleDirs_exist. exists new_sc.
  split; [exact HnewDir |].
  exists (ls1 ++ [seg1; seg2; seg3] ++ ls3).
  split; [exact HnewEmbed |].
  (* 局所置換によって開性を保存する。 *)
  apply (sub_in_triangle_keep_openness
           (l ++ [Plus] ++ r) (orn_seg segP)
           ls1 ls3 [segP] [seg1; seg2; seg3]);
    try assumption; try discriminate.
  - exact (sparse_embedding_single_sub_triangle ls1 segP ls3 HwholeSparse).
  - intros p Hp.
    apply (proj2 (single_sub_triangle segP p)).
    exact (Hin_triangle p Hp).
Qed.

Lemma AdmissibleDirs_r1_Minus_inv: forall l r,
  AdmissibleDirs (l ++ [Minus] ++ r) -> AdmissibleDirs (l ++ [Minus; Plus; Minus] ++ r).
Proof.
  intros l r admds.
  (* 疎な開埋め込みをとる *)
  destruct (AdmissibleDirs_has_sparse_embedding _ admds)
  as [ls [Hls [HwholeSparse Hext]]].
  destruct (embed_split l [Minus] r ls Hls)
  as [ls1 [ls2 [ls3 [Heq [Hls1 [Hls2 Hls3]]]]]].
  subst ls.
  destruct (embedding_one_dir Minus ls2 Hls2) as [segM HM].
  subst ls2.
  assert (Hne : ls1 ++ [segM] ++ ls3 <> []).
  { intro Hnil. apply app_eq_nil in Hnil as [_ Htail]. discriminate Htail. }
  pose proof (sparse_extensions_open _ _ Hne Hls HwholeSparse Hext) as Hopen.
  destruct Hls as [sc [Hdir_sc Hembed]].
  simpl in *.
  assert (H: embed_listDir (l ++ [Minus] ++ r) (ls1 ++ [segM] ++ ls3)). { (* scurve ではなく向き列の方が扱いやすい *)
    unfold embed_listDir. exists sc. split; assumption.
  }
  pose proof (embedding_M_to_MPM_in_triangle segM Hls2)
    as [seg1 [seg2 [seg3 [HMPM [Hin_triangle [Hinit_term Hslope]]]]]].
  assert (HreplacementOpen : ~ close [seg1; seg2; seg3]).
  { apply oneway_then_open.
    apply (embedding_oneway_listDir [Minus; Plus; Minus]); try assumption.
    apply MPM_is_oneway. }
  assert (Hboundary :
    primitive_segment (hd_segment [seg1; seg2; seg3]) = primitive_segment (hd_segment [segM])
    /\ primitive_segment (last_segment [seg1; seg2; seg3]) = primitive_segment (last_segment [segM])).
  { eapply contained_replacement_boundary_primitives
      with (ds := [Minus]) (ds' := [Minus; Plus; Minus]).
    - discriminate.
    - discriminate.
    - exact Hls2.
    - exact HMPM.
    - reflexivity.
    - reflexivity.
    - eapply alternating_embedding_contained; [exact Hls2 |].
      intros [|[|[|i]]] d d' Hd Hd'; simpl in *; try discriminate;
        inversion Hd; inversion Hd'; discriminate.
    - intros p Hp. exact (proj1 (Hin_triangle p Hp)).
    - exact Hinit_term. }
  destruct Hboundary as [HprimitiveHead HprimitiveLast].
  assert (HnewWhole : embed_listDir (l ++ [Minus; Plus; Minus] ++ r)
    (ls1 ++ [seg1; seg2; seg3] ++ ls3)).
  { rewrite (embedded_direction_list l ls1 Hls1),
      (embedded_direction_list r ls3 Hls3).
    eapply embedding_inner_change
      with (ds := l ++ [Minus] ++ r) (sub := [segM]);
      try assumption; try discriminate. }
  destruct HnewWhole as [new_sc [HnewDir HnewEmbed]].
  apply AdmissibleDirs_exist. exists new_sc.
  split; [exact HnewDir |].
  exists (ls1 ++ [seg1; seg2; seg3] ++ ls3).
  split; [exact HnewEmbed |].
  (* 局所置換によって開性を保存する。 *)
  apply (sub_in_triangle_keep_openness
           (l ++ [Minus] ++ r) (orn_seg segM)
           ls1 ls3 [segM] [seg1; seg2; seg3]);
    try assumption; try discriminate.
  - exact (sparse_embedding_single_sub_triangle ls1 segM ls3 HwholeSparse).
  - intros p Hp.
    apply (proj2 (single_sub_triangle segM p)).
    exact (Hin_triangle p Hp).
Qed.

Lemma AdmissibleDirs_r2_Plus: forall l r,
  AdmissibleDirs (l ++ [Plus; Plus; Minus; Minus] ++ r) -> AdmissibleDirs (l ++ [Plus; Minus] ++ r).
Proof.
  intros l r admds.
  (* 疎な開埋め込みをとる *)
  pose proof (embed_sparsely_listDir_PPMM _ _ admds) as H.
  destruct H as [ls1 [ls3 [seg1 [seg2 [seg3 [seg4 [Hcan [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [HwholeSparse [Hopen [Hsparse Hcontained]]]]]]]]]]]]]];
  simpl in *.
  pose proof (embedding_PPMM_to_PM_in_rect seg1 seg2 seg3 seg4 Hcan Hls2)
    as [seg1' [seg2' [HPM [Hin_rect [Hinit_term Hslope]]]]].
  assert (HwholeEmbed :
    embed_listDir (l ++ [Plus; Plus; Minus; Minus] ++ r)
      (ls1 ++ [seg1; seg2; seg3; seg4] ++ ls3)).
  { exists sc. split; assumption. }
  assert (Hboundary :
    primitive_segment (hd_segment [seg1'; seg2']) = primitive_segment (hd_segment [seg1; seg2; seg3; seg4])
    /\ primitive_segment (last_segment [seg1'; seg2']) = primitive_segment (last_segment [seg1; seg2; seg3; seg4])).
  { eapply contained_replacement_boundary_primitives
      with (ds := [Plus; Plus; Minus; Minus]) (ds' := [Plus; Minus]).
    - discriminate.
    - discriminate.
    - exact Hls2.
    - exact HPM.
    - reflexivity.
    - reflexivity.
    - exact Hcontained.
    - exact Hin_rect.
    - exact Hinit_term. }
  destruct Hboundary as [HprimitiveHead HprimitiveLast].
  assert (HnewWhole : embed_listDir (l ++ [Plus; Minus] ++ r)
    (ls1 ++ [seg1'; seg2'] ++ ls3)).
  { rewrite (embedded_direction_list l ls1 Hls1),
      (embedded_direction_list r ls3 Hls3).
    eapply embedding_inner_change
      with (ds := l ++ [Plus; Plus; Minus; Minus] ++ r) (sub := [seg1; seg2; seg3; seg4]);
      try assumption; try discriminate. }
  destruct HnewWhole as [new_sc [HnewDir HnewEmbed]].
  apply AdmissibleDirs_exist. exists new_sc.
  split; [exact HnewDir |].
  exists (ls1 ++ [seg1'; seg2'] ++ ls3).
  split; [exact HnewEmbed |].
  (* 局所置換によって開性を保存する。 *)
  apply (seg_in_rectangle_keep_openness
           (l ++ [Plus; Plus; Minus; Minus] ++ r)
           ls1 ls3 [seg1; seg2; seg3; seg4] [seg1'; seg2']);
    try assumption; try (symmetry; assumption); try congruence;
    try (apply in_rect_implies_or_endpoints; assumption).
  * apply oneway_then_open. apply (embedding_oneway_listDir [Plus; Minus]); try assumption.
  apply PM_is_oneway.
Qed.

Lemma AdmissibleDirs_r2_Minus: forall l r,
  AdmissibleDirs (l ++ [Minus; Minus; Plus; Plus] ++ r) -> AdmissibleDirs (l ++ [Minus; Plus] ++ r).
Proof.
  intros l r admds.
  (* 疎な開埋め込みをとる *)
  pose proof (embed_sparsely_listDir_MMPP _ _ admds) as H.
  destruct H as [ls1 [ls3 [seg1 [seg2 [seg3 [seg4 [Hcan [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [HwholeSparse [Hopen [Hsparse Hcontained]]]]]]]]]]]]]];
  simpl in *.
  pose proof (embedding_MMPP_to_MP_in_rect seg1 seg2 seg3 seg4 Hcan Hls2)
    as [seg1' [seg2' [HMP [Hin_rect [Hinit_term Hslope]]]]].
  assert (HwholeEmbed :
    embed_listDir (l ++ [Minus; Minus; Plus; Plus] ++ r)
      (ls1 ++ [seg1; seg2; seg3; seg4] ++ ls3)).
  { exists sc. split; assumption. }
  assert (Hboundary :
    primitive_segment (hd_segment [seg1'; seg2']) = primitive_segment (hd_segment [seg1; seg2; seg3; seg4])
    /\ primitive_segment (last_segment [seg1'; seg2']) = primitive_segment (last_segment [seg1; seg2; seg3; seg4])).
  { eapply contained_replacement_boundary_primitives
      with (ds := [Minus; Minus; Plus; Plus]) (ds' := [Minus; Plus]).
    - discriminate.
    - discriminate.
    - exact Hls2.
    - exact HMP.
    - reflexivity.
    - reflexivity.
    - exact Hcontained.
    - exact Hin_rect.
    - exact Hinit_term. }
  destruct Hboundary as [HprimitiveHead HprimitiveLast].
  assert (HnewWhole : embed_listDir (l ++ [Minus; Plus] ++ r)
    (ls1 ++ [seg1'; seg2'] ++ ls3)).
  { rewrite (embedded_direction_list l ls1 Hls1),
      (embedded_direction_list r ls3 Hls3).
    eapply embedding_inner_change
      with (ds := l ++ [Minus; Minus; Plus; Plus] ++ r) (sub := [seg1; seg2; seg3; seg4]);
      try assumption; try discriminate. }
  destruct HnewWhole as [new_sc [HnewDir HnewEmbed]].
  apply AdmissibleDirs_exist. exists new_sc.
  split; [exact HnewDir |].
  exists (ls1 ++ [seg1'; seg2'] ++ ls3).
  split; [exact HnewEmbed |].
  (* 局所置換によって開性を保存する。 *)
  apply (seg_in_rectangle_keep_openness
           (l ++ [Minus; Minus; Plus; Plus] ++ r)
           ls1 ls3 [seg1; seg2; seg3; seg4] [seg1'; seg2']);
    try assumption; try (symmetry; assumption); try congruence;
    try (apply in_rect_implies_or_endpoints; assumption).
  * apply oneway_then_open. apply (embedding_oneway_listDir [Minus; Plus]); try assumption.
  apply MP_is_oneway.
Qed.

Lemma AdmissibleDirs_r2_Plus_inv: forall l r,
  AdmissibleDirs (l ++ [Plus; Minus] ++ r) -> AdmissibleDirs (l ++ [Plus; Plus; Minus; Minus] ++ r).
Proof.
  intros l r admds.
  (* 疎な開埋め込みをとる *)
  destruct (AdmissibleDirs_has_prepared_PM l r admds)
  as [old_l [ls2 [old_r Hprepared]]].
  pose proof (embed_sparsely_if_both_lids_removable
  l [Plus; Minus] r old_l ls2 old_r Hprepared)
  as [ls1 [ls3 [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [_ [Hopen Hsparse]]]]]]]];
  simpl in *.
  assert (H: embed_listDir (l ++ [Plus; Minus] ++ r) (ls1 ++ ls2 ++ ls3)). { (* scurve ではなく向き列の方が扱いやすい *)
    unfold embed_listDir. exists sc. split; assumption.
  }
  pose proof (embedding_two_dir Plus Minus ls2 Hls2) as [seg1 [seg2 HPM]]; subst.
  pose proof (embedding_PM_to_PPMM_in_rect _ _ Hls2)
    as [seg1' [seg2' [seg3' [seg4' [HPPMM [Hin_rect [Hinit_term Hslope]]]]]]].
  assert (Hboundary :
    primitive_segment (hd_segment [seg1'; seg2'; seg3'; seg4']) = primitive_segment (hd_segment [seg1; seg2])
    /\ primitive_segment (last_segment [seg1'; seg2'; seg3'; seg4']) = primitive_segment (last_segment [seg1; seg2])).
  { eapply contained_replacement_boundary_primitives
      with (ds := [Plus; Minus]) (ds' := [Plus; Plus; Minus; Minus]).
    - discriminate.
    - discriminate.
    - exact Hls2.
    - exact HPPMM.
    - reflexivity.
    - reflexivity.
    - eapply alternating_embedding_contained; [exact Hls2 |].
      intros [|[|[|i]]] d d' Hd Hd'; simpl in *; try discriminate;
        inversion Hd; inversion Hd'; discriminate.
    - exact Hin_rect.
    - exact Hinit_term. }
  destruct Hboundary as [HprimitiveHead HprimitiveLast].
  assert (HnewWhole : embed_listDir (l ++ [Plus; Plus; Minus; Minus] ++ r)
    (ls1 ++ [seg1'; seg2'; seg3'; seg4'] ++ ls3)).
  { rewrite (embedded_direction_list l ls1 Hls1),
      (embedded_direction_list r ls3 Hls3).
    eapply embedding_inner_change
      with (ds := l ++ [Plus; Minus] ++ r) (sub := [seg1; seg2]);
      try assumption; try discriminate. }
  destruct HnewWhole as [new_sc [HnewDir HnewEmbed]].
  apply AdmissibleDirs_exist. exists new_sc.
  split; [exact HnewDir |].
  exists (ls1 ++ [seg1'; seg2'; seg3'; seg4'] ++ ls3).
  split; [exact HnewEmbed |].
  (* 局所置換によって開性を保存する。 *)
  apply (seg_in_rectangle_keep_openness
           (l ++ [Plus; Minus] ++ r) ls1 ls3 [seg1; seg2] _ );
    try assumption; try congruence;
    try (apply in_rect_implies_or_endpoints; assumption).
  * apply oneway_then_open. apply (embedding_oneway_listDir [Plus; Plus; Minus; Minus]); try assumption.
    apply PPMM_is_oneway.
Qed.

Lemma AdmissibleDirs_r2_Minus_inv: forall l r,
  AdmissibleDirs (l ++ [Minus; Plus] ++ r) -> AdmissibleDirs (l ++ [Minus; Minus; Plus; Plus] ++ r).
Proof.
  intros l r admds.
  (* 疎な開埋め込みをとる *)
  destruct (AdmissibleDirs_has_prepared_MP l r admds)
  as [old_l [ls2 [old_r Hprepared]]].
  pose proof (embed_sparsely_if_both_lids_removable
  l [Minus; Plus] r old_l ls2 old_r Hprepared)
  as [ls1 [ls3 [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [_ [Hopen Hsparse]]]]]]]];
  simpl in *.
  assert (H: embed_listDir (l ++ [Minus; Plus] ++ r) (ls1 ++ ls2 ++ ls3)). { (* scurve ではなく向き列の方が扱いやすい *)
    unfold embed_listDir. exists sc. split; assumption.
  }
  pose proof (embedding_two_dir Minus Plus ls2 Hls2) as [seg1 [seg2 HMP]]; subst.
  pose proof (embedding_MP_to_MMPP_in_rect _ _ Hls2)
    as [seg1' [seg2' [seg3' [seg4' [HMMPP [Hin_rect [Hinit_term Hslope]]]]]]].
  assert (Hboundary :
    primitive_segment (hd_segment [seg1'; seg2'; seg3'; seg4']) = primitive_segment (hd_segment [seg1; seg2])
    /\ primitive_segment (last_segment [seg1'; seg2'; seg3'; seg4']) = primitive_segment (last_segment [seg1; seg2])).
  { eapply contained_replacement_boundary_primitives
      with (ds := [Minus; Plus]) (ds' := [Minus; Minus; Plus; Plus]).
    - discriminate.
    - discriminate.
    - exact Hls2.
    - exact HMMPP.
    - reflexivity.
    - reflexivity.
    - eapply alternating_embedding_contained; [exact Hls2 |].
      intros [|[|[|i]]] d d' Hd Hd'; simpl in *; try discriminate;
        inversion Hd; inversion Hd'; discriminate.
    - exact Hin_rect.
    - exact Hinit_term. }
  destruct Hboundary as [HprimitiveHead HprimitiveLast].
  assert (HnewWhole : embed_listDir (l ++ [Minus; Minus; Plus; Plus] ++ r)
    (ls1 ++ [seg1'; seg2'; seg3'; seg4'] ++ ls3)).
  { rewrite (embedded_direction_list l ls1 Hls1),
      (embedded_direction_list r ls3 Hls3).
    eapply embedding_inner_change
      with (ds := l ++ [Minus; Plus] ++ r) (sub := [seg1; seg2]);
      try assumption; try discriminate. }
  destruct HnewWhole as [new_sc [HnewDir HnewEmbed]].
  apply AdmissibleDirs_exist. exists new_sc.
  split; [exact HnewDir |].
  exists (ls1 ++ [seg1'; seg2'; seg3'; seg4'] ++ ls3).
  split; [exact HnewEmbed |].
  (* 局所置換によって開性を保存する。 *)
  apply (seg_in_rectangle_keep_openness
           (l ++ [Minus; Plus] ++ r) ls1 ls3 [seg1; seg2] _ );
    try assumption; try congruence;
    try (apply in_rect_implies_or_endpoints; assumption).
  * apply oneway_then_open. apply (embedding_oneway_listDir [Minus; Minus; Plus; Plus]); try assumption.
    apply MMPP_is_oneway.
Qed.

Lemma AdmissibleDirs_preserve_Rule : forall l ds ds' r,
  Rule ds ds' 
	-> (AdmissibleDirs (l ++ ds ++ r) <-> AdmissibleDirs (l ++ ds' ++ r)).
Proof.
	intros l ds ds' r Hrule. inversion Hrule as [ HPMP HP | HMPM HM | HPPMM HPM | HMMPP HMP ]; subst. 
	- (* +-+ -> + *) split. apply AdmissibleDirs_r1_Plus. apply AdmissibleDirs_r1_Plus_inv.
	- (* -+- -> - *) split. apply AdmissibleDirs_r1_Minus. apply AdmissibleDirs_r1_Minus_inv.
	- (* ++-- -> +- *) split. apply AdmissibleDirs_r2_Plus. apply AdmissibleDirs_r2_Plus_inv.
	- (* --++ -> -+ *) split. apply AdmissibleDirs_r2_Minus. apply AdmissibleDirs_r2_Minus_inv.
Qed.

Lemma AdmissibleDirs_preserve_Step : forall ds ds',
	ReduceDirStep ds ds' 
	-> (AdmissibleDirs ds <-> AdmissibleDirs ds').
Proof.
  intros ds ds' Hstep.
  inversion Hstep ; subst.
  apply AdmissibleDirs_preserve_Rule. auto.
Qed.

Corollary AdmissibleDirs_preserve  : forall ds ds',
	ReduceDir ds ds' 
	-> (AdmissibleDirs ds <-> AdmissibleDirs ds').
Proof.
  intros ds ds' Hreduce.
  induction Hreduce.
  - (* RDRefl: ds = ds なので自明 *)
    reflexivity.
  - (* RDTrans: ds -> ds' -> ds'' の場合 *)
    apply (@iff_trans _ (AdmissibleDirs ds') _); try assumption.
		apply AdmissibleDirs_preserve_Step. assumption.
Qed.
