Require Export Sparse.ReconnectSplitProof.
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

Require Export Sparse.Classify.
(* ================================================================= *)
(* AdmissibleDirs について成り立ってほしい性質と，それに必要な補題 *)
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
(* 最終命題 *)
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
