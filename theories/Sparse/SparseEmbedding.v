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

Require Export Sparse.ReconnectSplitProof.
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

Local Lemma rotate_primitive_orn : forall g p,
  orn (rotate_primitive g p) = orn p.
Proof.
  intros g [[v h] c]. destruct g, v, h, c; reflexivity.
Qed.

Local Lemma rotate_primitive_dc : forall g p q,
  dc p q -> dc (rotate_primitive g p) (rotate_primitive g q).
Proof.
  intros g [[v1 h1] c1] [[v2 h2] c2] Hdc.
  destruct v1, h1, c1, v2, h2, c2;
    inversion Hdc; subst; destruct g; simpl; constructor.
Qed.

Local Lemma dc_successor_of_direction_unique : forall p q1 q2,
  dc p q1 -> dc p q2 -> orn q1 = orn q2 -> q1 = q2.
Proof.
  intros [[v h] c] [[v1 h1] c1] [[v2 h2] c2] H1 H2 Hdir.
  destruct v, h, c, v1, h1, c1, v2, h2, c2;
    inversion H1; inversion H2; subst; simpl in Hdir;
    try discriminate; reflexivity.
Qed.

Local Lemma same_orn_has_primitive_rotation : forall p q,
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

Local Lemma is_scurve_tail : forall p ps,
  is_scurve (p :: ps) -> is_scurve ps.
Proof.
  intros p ps H. inversion H; assumption.
Qed.

Local Lemma same_direction_scurve_lists_rotate : forall g p q ps qs,
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

Local Lemma follows_dir_rotate : forall g d p,
  follows_dir d p -> follows_dir (rotate_dir g d) (rotate_primitive g p).
Proof.
  intros g d [[v h] c] H.
  destruct g; destruct d as [vd | hd];
    try destruct vd; try destruct hd;
    destruct v; destruct h; destruct c; simpl in *;
    try discriminate; reflexivity.
Qed.

Local Lemma Forall_follows_dir_rotate : forall g d ps,
  Forall (follows_dir d) ps ->
  Forall (follows_dir (rotate_dir g d))
    (map (rotate_primitive g) ps).
Proof.
  intros g d ps H. induction H; simpl; constructor; auto.
  now apply follows_dir_rotate.
Qed.

Local Lemma is_one_way_scurve_dir_form : forall sc,
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

(* 最終命題 *)

(* 許容可能なら，全てのセグメント周りで疎な埋め込みが取れる *)
Lemma AdmissibleDirs_has_sparse_embedding :
  forall ds,
    AdmissibleDirs ds ->
    exists ls,
      embed_listDir ds ls
      /\ sparse_embedding ls
      /\ extensions_disjoint ls.
Admitted.

(* 選んだ同一の分割埋め込みが、全域疎性と非 x 単調の作業条件を満たす。 *)
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

(* 存在は任意の疎な埋め込みの回転ではなく、++-- 用に証人を選ぶ。
   +-+ は片側三角形の局所疎性が必要なので、ここでは扱わない。 *)
Lemma AdmissibleDirs_has_prepared_PPMM :
  forall ds1 ds2,
    AdmissibleDirs (ds1 ++ [Plus; Plus; Minus; Minus] ++ ds2) ->
    exists l sub r,
      PreparedSparseEmbedding ds1 [Plus; Plus; Minus; Minus] ds2 l sub r.
Admitted.

Lemma AdmissibleDirs_has_prepared_MMPP :
  forall ds1 ds2,
    AdmissibleDirs (ds1 ++ [Minus; Minus; Plus; Plus] ++ ds2) ->
    exists l sub r,
      PreparedSparseEmbedding ds1 [Minus; Minus; Plus; Plus] ds2 l sub r.
Admitted.

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

(* prepared 証人から、sub を固定して両側を再接続する。
   全域疎性と局所疎性を両方結論に残す。 *)
Lemma embed_sparsely_prepared_from_spec :
  forall ds1 sub_ds ds2 l sub r,
    PreparedSparseEmbedding ds1 sub_ds ds2 l sub r ->
    @ClassificationSpec l sub r (classify l sub r) ->
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
              (ordinary_reconnect_split l sub r h)).
    exact (prepared_ordinary_reconnect_preserves_embed
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
  { change (sparse_embedding (ordinary_reconnect_split l sub r h)).
    exact (prepared_no_lid_preserves_sparse_embedding
             (ds1 ++ sub_ds ++ ds2) l sub r h
             Hgeometry Hspec Hh Hsparse Hwhole Hext). }
  assert (Hext' : extensions_disjoint (l' ++ sub ++ r')).
  { change (extensions_disjoint (ordinary_reconnect_split l sub r h)).
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

(* 具体的な classify が Spec を満たす証明は、上の条件付き定理とは分離する。 *)
Lemma embed_sparsely_prepared :
  forall ds1 sub_ds ds2 l sub r,
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
  intros ds1 sub_ds ds2 l sub r Hprepared.
  eapply embed_sparsely_prepared_from_spec; [exact Hprepared |].
  destruct Hprepared as [_ _ _ Hwhole Hsparse Hext Hgeometry].
  exact (classify_spec l sub r Hgeometry Hsparse
           (ex_intro _ (ds1 ++ sub_ds ++ ds2) Hwhole) Hext).
Qed.

(* 両側の蓋を避けた prepared 証人がある場合の最終命題。
   証人選択と classify の仕様証明は、この命題の外に分離する。 *)
Proposition embed_sparsely_if_both_lids_removable
    (ds1 sub_ds ds2 : list Direction) :
  (exists l sub r, PreparedSparseEmbedding ds1 sub_ds ds2 l sub r) ->
  exists l r sub_ls,
    embed_listDir ds1 l
    /\ embed_listDir sub_ds sub_ls
    /\ embed_listDir ds2 r
    /\ embed_listDir (ds1 ++ sub_ds ++ ds2) (l ++ sub_ls ++ r)
    /\ sparse_embedding (l ++ sub_ls ++ r)
    /\ ~ close (l ++ sub_ls ++ r)
    /\ sparse_around l sub_ls r.
Proof.
  intros [l [sub [r Hprepared]]].
  destruct (embed_sparsely_prepared ds1 sub_ds ds2 l sub r Hprepared)
    as [l' [r' [Hl' [Hsub [Hr' [Hwhole [Hsparse [Hopen Haround]]]]]]]].
  exists l', r', sub.
  split; [exact Hl' |].
  split; [exact Hsub |].
  split; [exact Hr' |].
  split; [exact Hwhole |].
  split; [exact Hsparse |].
  split; [exact Hopen | exact Haround].
Qed.
