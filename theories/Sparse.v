Require Import Admissible.
Require Import Reduction.
Require Import Stdlib.Reals.Reals.
Require Import Embed.
Require Import PrimitiveSegment.
Require Import Segment.
Require Import ListExt.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.



(* ================================================================= *)
(*  0.  基本プリミティブ                                              *)
(* ================================================================= *)

Definition Point := (R * R)%type.
Definition Point_Set := Point -> Prop.

Definition hd_segment ls := hd default_segment ls.
Definition last_segment ls := last ls default_segment.

Parameter orn_seg   : Segment -> Direction.

Definition rightabove (rr1 rr2 : Point) :=
  let (x1, y1) := rr1 in
  let (x2, y2) := rr2 in x1 < x2 /\ y1 < y2.
Definition rightbelow (rr1 rr2 : Point) :=
  let (x1, y1) := rr1 in
  let (x2, y2) := rr2 in x1 < x2 /\ y2 < y1.

(* x 単調 = x 軸正の向きに進み続ける（y は無関係） *)
Definition x_monotone_seg  (s : Segment) : Prop := init_x s < term_x s.
Definition x_monotone_segs (ls : list Segment) : Prop :=
  forall s, In s ls -> x_monotone_seg s.

Definition connected (ls : list Segment) : Prop :=
  forall i s1 s2, nth_error ls i = Some s1 -> nth_error ls (S i) = Some s2 ->
    term s1 = init s2.

Definition onSegment' (seg: Segment) (rr : R * R) := exists (t:R), 0 < t <= 1 /\ point seg t = rr.
(* TODO: 空リストを省く *)
Definition onHead (seg: Segment) (rr : Point) := exists (t:R), t <= 0 /\ point seg t = rr.
Definition onHead_extend (ls: list Segment) (rr : Point) := onHead (hd_segment ls) rr.
Definition onLast (seg: Segment) (rr : Point) := exists (t:R), 1 < t /\ point seg t = rr.
Definition onLast_extend (ls: list Segment) (rr : Point) := onLast (last_segment ls) rr.
Definition onSegmentlist l rr := exists seg, In seg l /\ onSegment seg rr.
(* TODO: extend に関する公理を完成させた後， onExtendSegment と整合することを確認
		特に空リストの扱い *)
Definition onExtend ls rr := exists t, rr = extend ls t.

Definition same_extention_head ls1 ls2 := 
	(forall rr, onHead_extend ls1 rr <-> onHead_extend ls2 rr).
Definition same_extention_last ls1 ls2 := 
	(forall rr, onLast_extend ls1 rr <-> onLast_extend ls2 rr).


Definition embed_listDir (ds: list Direction) (ls: list Segment) : Prop :=
	exists sc: scurve, scurve_to_direction sc = ds
	/\ embed_scurve sc ls.

Definition is_one_way_embedding (ls : list Segment) : Prop :=
	exists sc, embed_scurve sc ls /\ is_one_way_scurve sc.
Definition is_one_way_listDir (ds: list Direction) : Prop :=
	exists sc: scurve, scurve_to_direction sc = ds /\ is_one_way_scurve sc.
(* 帰納的に定義することもできると思われる．
		特に後者は，回転数を使った定義もできる？
		必要があれば証明 *)


(* リスト補助（hd / last と map の交換．空リスト回避のため非空を仮定）*)
Lemma hd_map_nonnil :
  forall (f : Segment -> Segment) ls,
    ls <> [] -> hd_segment (map f ls) = f (hd_segment ls).
Proof.
  intros f ls H. destruct ls as [|a tl]; [contradiction | reflexivity].
Qed.

Lemma last_map_cons :
  forall (f : Segment -> Segment) a ls,
    last_segment (map f (a :: ls)) = f (last_segment (a :: ls)).
Proof.
  unfold last_segment. intros f a ls. revert a.
  induction ls as [|b tl IH]; intros a; simpl; [reflexivity|].
  exact (IH b).
Qed.

Lemma last_map_nonnil :
  forall (f : Segment -> Segment) ls,
    ls <> [] -> last_segment (map f ls) = f (last_segment ls).
Proof.
  intros f ls H. destruct ls as [|a tl]; [contradiction | apply last_map_cons].
Qed.

Lemma last_app_nonnil :
  forall (xs ys : list Segment),
    ys <> [] -> last_segment (xs ++ ys) = last_segment ys.
Proof.
  unfold last_segment. induction xs as [|a xs IH]; intros ys H; simpl; [reflexivity|].
  destruct (xs ++ ys) eqn:E.
  - destruct xs; destruct ys; simpl in E; try discriminate; contradiction.
  - rewrite <- E. apply IH; exact H.
Qed.

Lemma map_id_pointwise :
  forall (f : Segment -> Segment) (ls : list Segment),
    (forall s, In s ls -> f s = s) -> map f ls = ls.
Proof.
  induction ls as [|a tl IH]; intros H; simpl; [reflexivity|].
  rewrite H by (left; reflexivity).
  rewrite IH by (intros s Hs; apply H; right; exact Hs). reflexivity.
Qed.

Lemma last_In :
  forall (ls : list Segment),
    ls <> [] -> In (last_segment ls) ls.
Proof.
  intros ls H.
  apply exists_last in H.
  destruct H as [l' [b H]].
  rewrite H.
  unfold last_segment.
  rewrite last_last.
  apply in_or_app.
  right.
  constructor.
  reflexivity.
Qed.

Lemma nth_error_map_inv :
  forall (f : Segment -> Segment) ls n s,
    nth_error (map f ls) n = Some s ->
    exists s0, nth_error ls n = Some s0 /\ s = f s0.
Proof.
  intros f ls n s H. rewrite nth_error_map in H.
  destruct (nth_error ls n) as [s0|] eqn:E; simpl in H; [|discriminate].
  injection H as H. exists s0. split; [reflexivity | now symmetry].
Qed.

Lemma nth_error_lt : forall (ls : list Segment) i s,
  nth_error ls i = Some s -> (i < length ls)%nat.
Proof. intros ls i s H. apply nth_error_Some. rewrite H. discriminate. Qed.

Lemma nth_error_nth_eq : forall (ls : list Segment) i s d,
  nth_error ls i = Some s -> nth i ls d = s.
Proof.
  induction ls as [|a tl IH]; intros i s d H.
  - destruct i; simpl in H; discriminate.
  - destruct i as [|i]; simpl in H; simpl.
    + injection H as H; now subst.
    + now apply IH.
Qed.

Lemma app_split_eq : forall (A : Type) (l1 l2 m1 m2 : list A),
  l1 ++ l2 = m1 ++ m2 -> length l1 = length m1 -> l1 = m1 /\ l2 = m2.
Proof.
  intros A. induction l1 as [|a l1 IH]; intros l2 m1 m2 H HL.
  - destruct m1 as [|b m1]; simpl in *; [split; [reflexivity | exact H] | discriminate].
  - destruct m1 as [|b m1]; simpl in *; [discriminate|].
    injection H as Hab H. injection HL as HL.
    destruct (IH _ _ _ H HL) as [E1 E2].
    split; [f_equal; assumption | exact E2].
Qed.


(* onSegmentlist に関する補題 *)
Lemma onSegmentlist_init_hd :
  forall sub, sub <> [] -> onSegmentlist sub (init (hd_segment sub)).
Proof.
  intros sub H. destruct sub as [|a tl]; [contradiction|].
  exists a. split; [left; reflexivity|]. exists 0. split; [lra | reflexivity].
Qed.

Lemma onSegmentlist_term_last :
  forall sub, sub <> [] -> onSegmentlist sub (term (last_segment sub)).
Proof.
  intros sub H. exists (last_segment sub). split.
  - apply last_In. assumption.
  - exists 1. split; [lra | reflexivity].
Qed.

(* ---- 位置 -------------------------------------------------------- *)

Definition at_pos (ls : list Segment) (q : Pos) : Point :=
  point (nth (fst q) ls default_segment) (snd q).

Definition onExtAt (ls : list Segment) (i : nat) (p : Point) : Prop :=
  exists t, in_range ls (i, t) /\ at_pos ls (i, t) = p.

(* 隣接セグメントの共有端点（自己交差ではない）*)
Definition junction (ls : list Segment) (q1 q2 : Pos) : Prop :=
  (S (fst q1) = fst q2 /\ snd q1 = 1 /\ snd q2 = 0)
  \/ (S (fst q2) = fst q1 /\ snd q2 = 1 /\ snd q1 = 0).

Definition crossing (ls : list Segment) : Prop :=
  exists q1 q2, in_range ls q1 /\ in_range ls q2
             /\ at_pos ls q1 = at_pos ls q2
             /\ q1 <> q2.

(* in_range な2位置は決して junction をなさない *)
Lemma no_junction : forall ls q1 q2,
  in_range ls q1 -> in_range ls q2 -> ~ junction ls q1 q2.
Proof.
  intros ls q1 q2 [_ [H1 _]] [_ [H2 _]] [(Hs & Ha & Hb) | (Hs & Ha & Hb)].
  - destruct H2 as [H2|H2]; [rewrite H2 in Hs; discriminate | lra].
  - destruct H1 as [H1|H1]; [rewrite H1 in Hs; discriminate | lra].
Qed.

(* extend ls t は位置 pos_of ls t の点である *)
Lemma extend_at_pos : forall ls t,
  ls <> [] -> extend ls t = at_pos ls (pos_of ls t).
Proof.
  intros ls t Hne.
  destruct (extend_repr ls t Hne) as [s [Hnth Heq]].
  unfold at_pos, pos_of; simpl.
  rewrite (nth_error_nth_eq ls (extend_index ls t) s default_segment Hnth).
  exact Heq.
Qed.

(* その位置は in_range に入る（3つの領域すべてで確認）*)
Lemma pos_of_in_range : forall ls t, ls <> [] -> in_range ls (pos_of ls t).
Proof.
  intros ls t Hne.
  destruct (extend_repr ls t Hne) as [s [Hnth _]].
  unfold in_range, pos_of; simpl.
  split; [ eapply nth_error_lt; exact Hnth |].
  destruct (extend_param_region ls t Hne) as [Hmid | [[Hi Hle] | [Hi Hgt]]].
  - (* 0 < param <= 1 : 本体 *)      split; [right; lra | right; lra].
  - (* index = 0, param <= 0 : 先頭延長 *) split; [left; exact Hi | right; lra].
  - (* 末尾, 1 < param : 末尾延長 *)  split; [right; lra | left; exact Hi].
Qed.

(* ---- close との橋渡し（既存の close の定義に依存する唯一の箇所）--- *)
Lemma close_crossing : forall ls, ls <> [] -> close ls -> crossing ls.
Proof.
  intros ls Hne Hcl.
  unfold close, close_extended in Hcl.
  destruct Hcl as [t1 [t2 [Hne12 Heq]]].

  (* ★ rewrite は仮説側で行う（ゴールの形に依存しない） *)
  rewrite (extend_at_pos ls t1 Hne), (extend_at_pos ls t2 Hne) in Heq.

  assert (Hr1 : in_range ls (pos_of ls t1)) by (apply pos_of_in_range; exact Hne).
  assert (Hr2 : in_range ls (pos_of ls t2)) by (apply pos_of_in_range; exact Hne).
  assert (Hq : pos_of ls t1 <> pos_of ls t2).
  { intros Hq. apply Hne12.
    eapply extend_same_piece_injective; [exact Hne | |].
    - change (fst (pos_of ls t1) = fst (pos_of ls t2)). rewrite Hq; reflexivity.
    - change (snd (pos_of ls t1) = snd (pos_of ls t2)). rewrite Hq; reflexivity. }

  exists (pos_of ls t1), (pos_of ls t2).
  split; [exact Hr1 |].
  split; [exact Hr2 |].
  split; [exact Heq | exact Hq].
Qed.

Lemma crossing_close : forall ls, ls <> [] -> crossing ls -> close ls.
Proof.
  intros ls Hne (q1 & q2 & Hr1 & Hr2 & Hpt & Hq).
  destruct (extend_onto ls q1 Hne Hr1) as [t1 Ht1].
  destruct (extend_onto ls q2 Hne Hr2) as [t2 Ht2].
  unfold close, close_extended. exists t1, t2. split.
  - intros Ht. apply Hq. rewrite <- Ht1, <- Ht2, Ht. reflexivity.
  - rewrite (extend_at_pos ls t1 Hne), (extend_at_pos ls t2 Hne), Ht1, Ht2.
    exact Hpt.
Qed.

Corollary open_no_crossing : forall ls, ls <> [] -> ~ close ls -> ~ crossing ls.
Proof. intros ls Hne H Hc. apply H. apply crossing_close; assumption. Qed.


(* embed_scurve, listDir に関わる補題 *)
Definition nil_scurve : scurve := exist _ nil IsScurveNil.

Lemma proj1_nil_scurve : proj1_sig nil_scurve = nil.
Proof. reflexivity. Qed.

(* connect の定義（exist _ (ps :: proj1_sig lp) _）から定義的に成立 *)
Lemma proj1_connect : forall ps lp A,
  proj1_sig (connect ps lp A) = ps :: proj1_sig lp.
Proof. intros. reflexivity. Qed.

(* dc_pseg_hd は「相手リストの先頭だけ」を見る（DcNil / DcCons の形から）*)
Lemma dc_pseg_hd_hd_error : forall ps l1 l2,
  hd_error l1 = hd_error l2 -> dc_pseg_hd ps l1 -> dc_pseg_hd ps l2.
Proof.
  intros ps l1 l2 Hhd H. 
  destruct l1, l2; simpl in Hhd; inversion Hhd.
  - assumption.
  - subst.
    constructor.
    inversion H.
    assumption.
Qed.

(* scurve_to_direction = map f ∘ proj1_sig であることの帰結2本 *)
Lemma std_length : forall sc,
  length (scurve_to_direction sc) = length (proj1_sig sc).
Proof.
  intros.
  unfold scurve_to_direction; apply length_map.
Qed.

Lemma std_app_of_proj : forall sc sc1 sc2,
  proj1_sig sc = proj1_sig sc1 ++ proj1_sig sc2 ->
  scurve_to_direction sc = scurve_to_direction sc1 ++ scurve_to_direction sc2.
Proof.
  intros.
  unfold scurve_to_direction; intros; rewrite H; apply map_app.
Qed.

Lemma embed_scurve_length : forall sc ls,
  embed_scurve sc ls -> length (proj1_sig sc) = length ls.
Proof.
  intros sc ls H. induction H as
    [ | ps s He | ps lp A s1 s2 ls' He Hsub IH Hcon ].
  - reflexivity.
  - rewrite proj1_connect. fold nil_scurve; rewrite proj1_nil_scurve. reflexivity.
  - rewrite proj1_connect. simpl. f_equal. exact IH.
Qed.

Lemma embed_scurve_split : forall n sc ls,
  embed_scurve sc ls ->
  exists sc1 sc2 l1 l2,
       ls = l1 ++ l2
    /\ proj1_sig sc = proj1_sig sc1 ++ proj1_sig sc2
    /\ length (proj1_sig sc1) = Nat.min n (length (proj1_sig sc))
    /\ embed_scurve sc1 l1
    /\ embed_scurve sc2 l2.
Proof.
  induction n as [|n' IH]; intros sc ls H.

  (* ---- n = 0 : 何も取らない ---- *)
  - exists nil_scurve, sc, nil, ls.
    split; [reflexivity |].
    split; [reflexivity |].
    split; [reflexivity |].
    split; [exact EmbedScurveNil | exact H].

  (* ---- n = S n' ---- *)
  - destruct H as
      [ | ps s He | ps lp A s1 s2 ls' He Hsub Hcon ].

    (* 空曲線 *)
    + exists nil_scurve, nil_scurve, nil, nil.
      split; [reflexivity |].
      split; [reflexivity |].
      split; simpl; auto.
      split; exact EmbedScurveNil.

    (* 1本だけ：全部取る *)
    + exists (connect ps nil_scurve (DcNil ps)), nil_scurve, (s :: nil), nil.
      split; [reflexivity |].
      split; [rewrite proj1_connect, proj1_nil_scurve; reflexivity |].
      split.
      { rewrite proj1_connect, proj1_nil_scurve. simpl.
        rewrite Nat.min_r; [reflexivity | lia]. }
      split; [exact (EmbedScurveSigle ps s He) | exact EmbedScurveNil].

    (* 2本以上：先頭 ps を1つ取り、残りを IH で分割 *)
    + destruct (IH lp (s2 :: ls') Hsub)
        as (sc1' & sc2' & l1' & l2' & Els & Eps & Elen & Hc1 & Hc2).
      destruct (proj1_sig sc1') as [|q rest] eqn:Eq.

      (* (a) IH 側の前半が空 ⇒ 取るのは s1 だけ *)
      * assert (Hl1 : (length l1' = 0)%nat).
        { rewrite <- (embed_scurve_length _ _ Hc1), Eq. reflexivity. }
        destruct l1' as [|w tl]; simpl in Hl1; [| discriminate].
        simpl in Els. subst l2'.
        exists (connect ps nil_scurve (DcNil ps)), lp, (s1 :: nil), (s2 :: ls').
        split; [reflexivity |].
        split; [rewrite !proj1_connect, proj1_nil_scurve; reflexivity |].
        split.
        { rewrite !proj1_connect, proj1_nil_scurve. simpl.
          rewrite <- Elen. reflexivity. }
        split; [exact (EmbedScurveSigle ps s1 He) | exact Hsub].

      (* (b) IH 側の前半が非空 ⇒ ps を前に付け足す *)
      * assert (Hl1 : length l1' = S (length rest)).
        { rewrite <- (embed_scurve_length _ _ Hc1), Eq. reflexivity. }
        destruct l1' as [|w tl]; simpl in Hl1; [discriminate |].
        injection Els as Ew Els'. subst w.

        assert (Hhd : hd_error (proj1_sig lp) = hd_error (proj1_sig sc1')).
        { rewrite Eps, Eq. reflexivity. }
        assert (A' : dc_pseg_hd ps (proj1_sig sc1'))
          by (eapply dc_pseg_hd_hd_error; [exact Hhd | exact A]).

        exists (connect ps sc1' A'), sc2', (s1 :: s2 :: tl), l2'.
        split; [simpl; f_equal; f_equal; exact Els' |].
        split; [rewrite !proj1_connect, Eps, app_comm_cons; congruence|].
        split.
        { rewrite !proj1_connect. simpl. rewrite Eq, Elen. reflexivity. }
        split.
        { exact (EmbedScurveCons ps sc1' A' s1 s2 tl He Hc1 Hcon). }
        { exact Hc2. }
Qed.

(* ---- embed の分解 --------------------- *)
Lemma embed_split2 : forall ds1 ds2 ls,
  embed_listDir (ds1 ++ ds2) ls ->
  exists l1 l2, ls = l1 ++ l2 /\ embed_listDir ds1 l1 /\ embed_listDir ds2 l2.
Proof.
  intros ds1 ds2 ls [sc [Hdir Hemb]].
  destruct (embed_scurve_split (length ds1) sc ls Hemb)
    as (sc1 & sc2 & l1 & l2 & Els & Eps & Elen & H1 & H2).

  assert (Hd : scurve_to_direction sc
               = scurve_to_direction sc1 ++ scurve_to_direction sc2)
    by (apply std_app_of_proj; exact Eps).

  assert (Htot : (length (proj1_sig sc) = length ds1 + length ds2)%nat).
  { rewrite <- std_length, Hdir, length_app. reflexivity. }

  assert (Elen1 : length (scurve_to_direction sc1) = length ds1).
  { rewrite std_length, Elen, Htot. apply Nat.min_l, Nat.le_add_r. }

  rewrite Hdir in Hd.
  destruct (app_split_eq _ ds1 ds2 _ _ Hd (eq_sym Elen1)) as [E1 E2].

  exists l1, l2.
  split; [exact Els |].
  split.
  - exists sc1. split; [symmetry; exact E1 | exact H1].
  - exists sc2. split; [symmetry; exact E2 | exact H2].
Qed.

Lemma embed_split :
  forall ds1 sub_ds ds2 ls,
    embed_listDir (ds1 ++ sub_ds ++ ds2) ls ->
    exists l sub r,
      ls = l ++ sub ++ r
      /\ embed_listDir ds1 l /\ embed_listDir sub_ds sub /\ embed_listDir ds2 r.
Proof.
  intros ds1 sub_ds ds2 ls H.
  destruct (embed_split2 ds1 (sub_ds ++ ds2) ls H) as (l & m & Elm & Hl & Hm).
  destruct (embed_split2 sub_ds ds2 m Hm) as (sub & r & Em & Hsub & Hr).
  exists l, sub, r.
  split; [rewrite Elm, Em; reflexivity |].
  split; [exact Hl |].
  split; [exact Hsub | exact Hr].
Qed.


Lemma scurve_listDir_length_consis: forall ds sc,
  scurve_to_direction sc = ds -> length ds = length (proj1_sig sc).
Proof.
	intros ds. unfold scurve_to_direction. 
	induction ds as [ | d ds' IH];  intros sc H.
	- (* ds = [] *) 
		destruct (proj1_sig sc); [auto | discriminate].
	- (* ds = d::ds' *) 
		destruct sc as [sc' Hsc].
		destruct Hsc as [ | p ps Hps H0]; try discriminate.
		simpl; f_equal.
		apply (IH (exist _ _ Hps)).
		simpl in *.
		injection H; auto.
Qed.

(* 向き列の長さとセグメント列の長さは一致する *)
Lemma embedding_listDir_length_consis: forall (ds: list Direction) (ls: list Segment),
  embed_listDir ds ls -> length ds = length ls.
Proof.
	intros ds ls [sc [Hdir Hembed]].
	rewrite (scurve_listDir_length_consis _ _ Hdir).
	apply scurve_length_consis.
	auto.
Qed.

Lemma embed_nonnil :
  forall ds ls, embed_listDir ds ls -> ds <> [] -> ls <> [].
Proof.
  intros ds ls Hembed Hds Hls.
  apply embedding_listDir_length_consis in Hembed.
  apply Hds.
  subst.
  apply length_zero_iff_nil.
  auto. 
Qed.

(* 単方向な向き列は空でない（is_one_way_scurve の定義から）*)
Lemma one_way_listDir_nonnil :
  forall ds, is_one_way_listDir ds -> ds <> [].
Proof.
  intros ds H contra.
  destruct H as [sc [Hdir Honeway]].
  destruct Honeway as [Hnonnil _].
  apply Hnonnil.
  subst.
  apply scurve_listDir_length_consis in contra.
  apply length_zero_iff_nil.
  auto.
Qed.

Lemma open_nonnil : forall ls, ~ close ls -> ls <> [].
Admitted.

(*  「向き列が同じで、長さが同じで、連結なら、同じ ds の埋め込み」 *)
Lemma embed_scurve_transfer : forall ds ls ls',
  embed_listDir ds ls ->
  length ls' = length ls ->
  (forall i s s', nth_error ls i = Some s -> nth_error ls' i = Some s' ->
                  orn_seg s' = orn_seg s) ->
  connected ls' ->
  embed_listDir ds ls'.
Admitted.

(* ---- 連結性は埋め込みから出る（Embed.v の consist_init_term）---- *)
Lemma embed_listDir_connected : forall ds ls, embed_listDir ds ls -> connected ls.
Admitted.



(* ================================================================= *)
(*  1．回転（90°×4）—                                                   *)
(*      8方向はどれも 90°の4回転のどれかで x 正成分を持つ向きに入る．    *)
(* ================================================================= *)

Inductive Rot : Type := R0 | R90 | R180 | R270.

Definition rot_pt (g : Rot) (p : Point) : Point :=
  match g with
  | R0   => p
  | R90  => (- snd p, fst p)
  | R180 => (- fst p, - snd p)
  | R270 => (snd p, - fst p)
  end.

(* TODO : 反転は不要かもしれない *)
Definition rot_inv (g : Rot) : Rot :=
  match g with R0 => R0 | R90 => R270 | R180 => R180 | R270 => R90 end.

Lemma rot_pt_inv : forall g p, rot_pt (rot_inv g) (rot_pt g p) = p.
Proof.
  intros g [x y]; destruct g; simpl;
    f_equal; try ring.
Qed.

(* セグメントの回転．point との整合を公理に置くと                *)
(* onSegment / onHead / onLast の輸送が自動で従う                      *)
Parameter rot_seg : Rot -> Segment -> Segment.
Definition rot_segs (g : Rot) (ls : list Segment) := map (rot_seg g) ls.

Axiom rot_seg_point :
  forall g s t, point (rot_seg g s) t = rot_pt g (point s t).
Axiom rot_inv_seg :
  forall g s, rot_seg (rot_inv g) (rot_seg g s) = s.
Axiom rot_seg_inv :
  forall g s, rot_seg g (rot_seg (rot_inv g) s) = s.

Lemma rot_inv_segs : forall g ls, rot_segs (rot_inv g) (rot_segs g ls) = ls.
Proof.
  intros g ls. unfold rot_segs. rewrite map_map.
  apply map_id_pointwise. intros s _. apply rot_inv_seg.
Qed.

Lemma rot_segs_inv : forall g ls, rot_segs g (rot_segs (rot_inv g) ls) = ls.
Proof.
  intros g ls. unfold rot_segs. rewrite map_map.
  apply map_id_pointwise. intros s _. apply rot_seg_inv.
Qed.

Lemma rot_segs_app :
  forall g ls1 ls2, rot_segs g (ls1 ++ ls2) = rot_segs g ls1 ++ rot_segs g ls2.
Proof. intros. unfold rot_segs. apply map_app. Qed.

(* ---- 回転の反転 ------------------------------------------------- *)
Lemma rot_inv_inv : forall g, rot_inv (rot_inv g) = g.
Proof. destruct g; reflexivity. Qed.

(* ---- 非空性 ----------------------------------------------------- *)
Lemma rot_segs_nonnil : forall g ls, ls <> [] -> rot_segs g ls <> [].
Proof.
  intros g ls H. destruct ls as [|a tl]; [contradiction|].
  unfold rot_segs. simpl. discriminate.
Qed.

Lemma app_nonnil_mid :
  forall (l sub r : list Segment), sub <> [] -> l ++ sub ++ r <> [].
Proof.
  intros l sub r H. destruct l as [|a l']; simpl.
  - destruct sub as [|s sub']; [contradiction | discriminate].
  - discriminate.
Qed.

(* --- 点集合の輸送 --- *)
Lemma onSegment_rot :
  forall g s p, onSegment s p -> onSegment (rot_seg g s) (rot_pt g p).
Proof.
  intros g s p [t [Ht Hp]]. exists t. split; [exact Ht|].
  rewrite rot_seg_point, Hp. reflexivity.
Qed.

Lemma onHead_rot :
  forall g s p, onHead s p -> onHead (rot_seg g s) (rot_pt g p).
Proof.
  intros g s p [t [Ht Hp]]. exists t. split; [exact Ht|].
  rewrite rot_seg_point, Hp. reflexivity.
Qed.

Lemma onLast_rot :
  forall g s p, onLast s p -> onLast (rot_seg g s) (rot_pt g p).
Proof.
  intros g s p [t [Ht Hp]]. exists t. split; [exact Ht|].
  rewrite rot_seg_point, Hp. reflexivity.
Qed.


Lemma Rmin_opp : forall a b, Rmin (- a) (- b) = - Rmax a b.
Proof. intros. unfold Rmin, Rmax. destruct (Rle_dec (-a) (-b)), (Rle_dec a b); lra. Qed.
Lemma Rmax_opp : forall a b, Rmax (- a) (- b) = - Rmin a b.
Proof. intros. unfold Rmin, Rmax. destruct (Rle_dec (-a) (-b)), (Rle_dec a b); lra. Qed.

(* --- embed / close / sparse の回転不変性 --- *)
Lemma rot_embed :
  forall g ds ls, embed_listDir ds ls -> embed_listDir ds (rot_segs g ls).
Admitted. 

Lemma rot_close :
  forall g ls, close (rot_segs g ls) -> close ls.
Admitted.  (* rot_pt が単射なので，交点は交点に対応 *)

Lemma rot_open :
  forall g ls, ~ close ls -> ~ close (rot_segs g ls).
Proof. intros g ls H Hc. apply H. eapply rot_close; exact Hc. Qed.

(* --- 単方向なら回転で x 正方向単調にできる --- *)
Lemma one_way_rot_exists :
  forall sub, is_one_way_embedding sub ->
    exists g : Rot, x_monotone_segs (rot_segs g sub).
Admitted.
(* 証明方針：is_one_way_scurve から，sub の全セグメントの向きは        *)
(*   「ある成分の符号が一定」な向きの集合に入る．8方向 d に対し，        *)
(*   g だけ回転させて {E, NE, SE}（= x 正成分）に入る g が存在：         *)
(*     E,NE,SE → R0 ／ N,NW → R270 ／ W,SW → R180 ／ S → R90          *)
(*   あとは rot_seg_point から init_x < term_x を計算するだけ．        *)

    
(* --------------------------------------------------------------------------- *)
(* AdmissibleDirs について成り立ってほしい性質と，それに必要な補題 *)

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
	  admit.
	- auto. 
Admitted.

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
(*  2．長方形と sparse                               *)
(* ================================================================= *)

Record Rect := mkRect { rx0 : R; ry0 : R; rx1 : R; ry1 : R }.

(* 曲線の始点と終点を結んだ線分を対角線にもつ矩形．部分曲線を含むとは限らない *)
(* TODO: 空リストを含まない方が良い *)
Definition rect_of (sub : list Segment) : Rect :=
  let q0 := init (hd_segment sub) in
  let q3 := term (last_segment sub) in
  mkRect (Rmin (fst q0) (fst q3)) (Rmin (snd q0) (snd q3))
         (Rmax (fst q0) (fst q3)) (Rmax (snd q0) (snd q3)).

(* 開長方形（境界ケースを避けられる） *)
Definition in_rect (Rc : Rect) (p : Point) : Prop :=
  rx0 Rc < fst p < rx1 Rc /\ ry0 Rc < snd p < ry1 Rc.

Definition rect_width  (Rc : Rect) : R := rx1 Rc - rx0 Rc.
Definition rect_height (Rc : Rect) : R := ry1 Rc - ry0 Rc.

Definition sparse (l sub r : list Segment) : Prop :=
  let Rc := rect_of sub in
    (forall p, onHead_extend (l ++ sub ++ r) p
    \/ onSegmentlist (l ++ r) p
    \/ onLast_extend (l ++ sub ++ r) p -> ~ in_rect Rc p).
  
Lemma rect_dims_nonneg :
  forall sub, 0 <= rect_width (rect_of sub) /\ 0 <= rect_height (rect_of sub).
Proof.
  intros sub. unfold rect_width, rect_height, rect_of. simpl.
  pose proof (Rmin_l (fst (init (hd_segment sub))) (fst (term (last_segment sub)))).
  pose proof (Rmax_l (fst (init (hd_segment sub))) (fst (term (last_segment sub)))).
  pose proof (Rmin_l (snd (init (hd_segment sub))) (snd (term (last_segment sub)))).
  pose proof (Rmax_l (snd (init (hd_segment sub))) (snd (term (last_segment sub)))).
  split; lra.
Qed.


(* --- 長方形の輸送（ sparse の回転不変性の核）--- *)
Definition rot_rect (g : Rot) (Rc : Rect) : Rect :=
  match g with
  | R0   => Rc
  | R90  => mkRect (- ry1 Rc) (rx0 Rc) (- ry0 Rc) (rx1 Rc)
  | R180 => mkRect (- rx1 Rc) (- ry1 Rc) (- rx0 Rc) (- ry0 Rc)
  | R270 => mkRect (ry0 Rc) (- rx1 Rc) (ry1 Rc) (- rx0 Rc)
  end.

Lemma in_rect_rot :
  forall g Rc p, in_rect (rot_rect g Rc) (rot_pt g p) <-> in_rect Rc p.
Proof.
  intros g Rc [x y]. destruct g; unfold in_rect, rot_rect; simpl; split; intros; lra.
Qed.


Lemma rect_of_rot :
  forall g sub, sub <> [] -> rect_of (rot_segs g sub) = rot_rect g (rect_of sub).
Proof.
  intros g sub H. unfold rect_of, rot_segs.
  rewrite (hd_map_nonnil _ _ H), (last_map_nonnil _ _ H).
  unfold init, term. rewrite !rot_seg_point.
  destruct g; simpl; unfold rot_rect; simpl;
    rewrite ?Rmin_opp, ?Rmax_opp; reflexivity.
Qed.
(* ↑ min/max の並び替えで rewrite の向きを微調整する必要あり（要確認）*)

(* not used *)
Lemma rot_sparse :
  forall g l sub r, sub <> [] ->
    sparse (rot_segs g l) (rot_segs g sub) (rot_segs g r) -> sparse l sub r.
Proof.
  intros g l sub r Hsub Hsp p Hp Hin.
  pose proof (app_nonnil_mid l sub r Hsub) as Hall.
  apply (Hsp (rot_pt g p)).
  - destruct Hp as [Hh | [Hm | Hl]].
    + left. unfold onHead_extend in *.
      rewrite <- !rot_segs_app.
      unfold rot_segs.
      rewrite (hd_map_nonnil _ _ Hall).
      apply onHead_rot; exact Hh.
    + right; left. destruct Hm as [s [Hs Hps]].
      exists (rot_seg g s). split.
      * rewrite <- rot_segs_app. apply in_map; exact Hs.
      * apply onSegment_rot; exact Hps.
    + right; right. unfold onLast_extend in *.
      rewrite <- !rot_segs_app.
      unfold rot_segs.
      rewrite (last_map_nonnil _ _ Hall).
      apply onLast_rot; exact Hl.
  - rewrite (rect_of_rot g sub Hsub). apply in_rect_rot. exact Hin.
Qed.


(* ================================================================= *)
(*  3.  境界線                *)
(* ================================================================= *)

(* 境界線ならば関数だが，関数ならば境界線ではないので
   Border に関する変な補題をつくらないよう注意．
   特に [forall b : Border, ...] は原則としてつくらない *)
Definition Border := R -> R. 
Definition on_border (b : Border) (p : Point) : Prop := snd p = b (fst p).

(* 曲線全体と簡約対象 sub から境界線を1つ決める *)
(* 簡約部分が左下から右上にx軸に関して単調に向かうものとした時，
    境界線として，
    1. 左下からx軸負の向きに進む限り，セグメントないし延長線に沿う
    2. x軸正の向きに進みそうになったらセグメント上を脱出し，x軸負の向きに進む
    3. その後セグメントないし延長線に当たりそうになったら，その十分近くを沿ってx軸負の向きに進む
    4. x軸正の向きに進みそうになったらセグメントないし延長線を横断し，（この時の交点で，傾きが無限大のはずである）
      そのままx軸負の向きに進む
    5. 向かう先にセグメントないし延長線がないならそのまま半直線を伸ばす．あるなら 3. に戻る *)
Parameter make_border : list Segment -> list Segment -> Border.

(* 3分割された形での省略記法 *)
Definition border_of (l sub r : list Segment) : Border :=
  make_border (l ++ sub ++ r) sub.

(* 点集合 P が境界線より上／下（以上／以下） *)
Definition weakly_above (b : Border) (P : Point_Set) : Prop :=
  forall p, P p -> b (fst p) <= snd p.
Definition weakly_below (b : Border) (P : Point_Set) : Prop :=
  forall p, P p -> snd p <= b (fst p).

(* 可変域：曲線 ctx の中でセグメント s が形を変えてよい領域 *)
(* TODO : 可変域が取れるのは自己交差がない場合のみ *)
Parameter dzone : list Segment -> list Segment -> nat -> Point_Set.

(* ---- 可変域には自分と隣接セグメント以外は入らない ---------- *)
(* 可変域は端点を含む必要があることに注意
  （境界線と交わるセグメントの調整に使う時，移動後の端点の近くを通るように調整する） *)
Lemma dz_local : forall l sub r i j p, 
  let ctx := (l ++ sub ++ r) in
  ~ close ctx ->
  (i < length ctx)%nat -> (j < length ctx)%nat ->
  dzone ctx sub i p -> onExtAt ctx j p -> 
  (i = j \/ S i = j \/ i = S j).
Admitted.

  (* --- 境界線との接触点の x 座標 --- *)
Definition contact_x (b : Border) (P : Point_Set) (x : R) : Prop :=
  exists p, P p /\ on_border b p /\ fst p = x.

(* sub を完全に覆う長方形（sub のみに依存）*)
(* y軸方向への移動はこの長方形の高さ以上必要 *)
Parameter bbox_of : list Segment -> Rect.
Axiom bbox_of_bounds :
  forall sub p, onSegmentlist sub p ->
    ry0 (bbox_of sub) <= snd p <= ry1 (bbox_of sub).

Definition outside_rect_x (sub : list Segment) (x : R) : Prop :=
  x < rx0 (rect_of sub) \/ rx1 (rect_of sub) < x.

(* 境界線を作るための前提（これ以外の仮定は使わない）*)
Definition well_split (l sub r : list Segment) : Prop :=
  sub <> [] /\ x_monotone_segs sub /\ ~ close (l ++ sub ++ r).

(* h の条件（sub のみに依存．境界線に依存しない）*)
Definition h_large (h : R) (sub : list Segment) : Prop :=
  0 < h /\ rect_height (bbox_of sub) < h.

Lemma choose_h : forall sub, exists h, h_large h sub.
Proof.
  intros sub. exists (Rmax 1 (rect_height (bbox_of sub) + 1)).
  unfold h_large. split.
  - eapply Rlt_le_trans; [apply Rlt_0_1 | apply Rmax_l].
  - eapply Rlt_le_trans; [| apply Rmax_r]. lra.
Qed.

(* make_border の満たすべき性質 *)
(* ---- (A-1) sub は境界線のグラフの一部 -------------------- *)
Lemma mb_fits :
  forall l sub r, well_split l sub r ->
    forall p, onSegmentlist sub p -> on_border (border_of l sub r) p.
Admitted.

(* ---- (A-2) 長方形の x 範囲では，境界線は sub のグラフそのもの ----- *)
(*      x 単調性＋連結性＋中間値定理（mb_fits から従う独立補題）      *)
Lemma mb_cover :
  forall l sub r, well_split l sub r ->
    forall x, rx0 (rect_of sub) <= x <= rx1 (rect_of sub) ->
      exists q, onSegmentlist sub q /\ fst q = x
                /\ snd q = border_of l sub r x.
Admitted.

(* ---- (A-3) l, r の各セグメントは境界線を横断しない --------------- *)
Lemma mb_side :
  forall l sub r, well_split l sub r ->
    forall s, In s (l ++ r) ->
      weakly_above (border_of l sub r) (onSegment s)
      \/ weakly_below (border_of l sub r) (onSegment s).
Admitted.

(* ---- (A-4) 延長線（半直線）も横断しない -------------------------- *)
Lemma mb_side_head :
  forall l sub r, well_split l sub r ->
      weakly_above (border_of l sub r) (onHead_extend (l ++ sub ++ r))
   \/ weakly_below (border_of l sub r) (onHead_extend (l ++ sub ++ r)).
Admitted.

Lemma mb_side_last :
  forall l sub r, well_split l sub r ->
      weakly_above (border_of l sub r) (onLast_extend (l ++ sub ++ r))
   \/ weakly_below (border_of l sub r) (onLast_extend (l ++ sub ++ r)).
Admitted.

(* ---- (A-5) 境界線に触る x は長方形の x 範囲の外 ------------------ *)
Lemma mb_ct_seg :
  forall l sub r, well_split l sub r ->
    forall x, contact_x (border_of l sub r) (onSegmentlist (l ++ r)) x ->
      outside_rect_x sub x.
Admitted.

Lemma mb_ct_head :
  forall l sub r, well_split l sub r ->
    forall x, contact_x (border_of l sub r)
                        (onHead_extend (l ++ sub ++ r)) x ->
      outside_rect_x sub x.
Admitted.

Lemma mb_ct_last :
  forall l sub r, well_split l sub r ->
    forall x, contact_x (border_of l sub r)
                        (onLast_extend (l ++ sub ++ r)) x ->
      outside_rect_x sub x.
Admitted.

Lemma rect_of_in_bbox :
  forall sub, sub <> [] ->
    ry0 (bbox_of sub) <= ry0 (rect_of sub)
    /\ ry1 (rect_of sub) <= ry1 (bbox_of sub).
Proof.
  intros sub H.
  pose proof (bbox_of_bounds sub _ (onSegmentlist_init_hd sub H)) as [A1 A2].
  pose proof (bbox_of_bounds sub _ (onSegmentlist_term_last sub H)) as [B1 B2].
  unfold rect_of; simpl. unfold Rmin, Rmax.
  destruct (Rle_dec (snd (init (hd_segment sub))) (snd (term (last_segment sub))));
    split; lra.
Qed.


(* ================================================================= *)
(*  4.  上下移動                                   *)
(* ================================================================= *)

Inductive Region : Type := RegFix | RegUp | RegDown.

(* 境界線との上下比較だけで決まる *)
Definition classify (b : Border) (p : Point) : Region :=
  if Rlt_dec (b (fst p)) (snd p) then RegUp
  else if Rlt_dec (snd p) (b (fst p)) then RegDown
  else RegFix.

Definition shift (h : R) (g : Region) (p : Point) : Point :=
  match g with
  | RegFix  => p
  | RegUp   => (fst p, snd p + h)
  | RegDown => (fst p, snd p - h)
  end.

Definition operate_point (b : Border) (h : R) (p : Point) : Point :=
  shift h (classify b p) p.

Lemma classify_RegFix_char :
  forall b p, classify b p = RegFix -> on_border b p.
Proof.
  intros b p H. unfold classify in H. unfold on_border.
  destruct (Rlt_dec (b (fst p)) (snd p)); [discriminate|].
  destruct (Rlt_dec (snd p) (b (fst p))); [discriminate|]. lra.
Qed.

Lemma classify_RegUp_char :
  forall b p, classify b p = RegUp -> b (fst p) < snd p.
Proof.
  intros b p H. unfold classify in H.
  destruct (Rlt_dec (b (fst p)) (snd p)); [assumption|].
  destruct (Rlt_dec (snd p) (b (fst p))); discriminate.
Qed.

Lemma classify_RegDown_char :
  forall b p, classify b p = RegDown -> snd p < b (fst p).
Proof.
  intros b p H. unfold classify in H.
  destruct (Rlt_dec (b (fst p)) (snd p)); [discriminate|].
  destruct (Rlt_dec (snd p) (b (fst p))); [assumption|discriminate].
Qed.

Lemma op_fixes_RegFix :
  forall b h p, classify b p = RegFix -> operate_point b h p = p.
Proof. intros b h p H. unfold operate_point. rewrite H. reflexivity. Qed.

  Lemma classify_on_border : forall b p, on_border b p -> classify b p = RegFix.
Proof.
  intros b p H. unfold on_border in H. unfold classify.
  destruct (Rlt_dec (b (fst p)) (snd p)); [lra|].
  destruct (Rlt_dec (snd p) (b (fst p))); [lra | reflexivity].
Qed.

Lemma operate_point_border : forall b h p,
  on_border b p -> operate_point b h p = p.
Proof.
  intros b h p H. unfold operate_point.
  rewrite (classify_on_border b p H). reflexivity.
Qed.

Lemma shift_fst : forall h g p, fst (shift h g p) = fst p.
Proof. intros h g p. destruct g; reflexivity. Qed.

(* ★ 単射性 *)
Lemma operate_point_inj : forall b h p q,
  0 < h -> operate_point b h p = operate_point b h q -> p = q.
Proof.
  intros b h p q Hh H.
  assert (Hx : fst p = fst q).
  { unfold operate_point in H.
    rewrite <- (shift_fst h (classify b p) p), <- (shift_fst h (classify b q) q).
    rewrite H. reflexivity. }
  assert (Hs : snd (shift h (classify b p) p) = snd (shift h (classify b q) q))
    by (unfold operate_point in H; rewrite H; reflexivity).
  apply injective_projections; [exact Hx |].
  destruct (classify b p) eqn:Hp, (classify b q) eqn:Hq; simpl in Hs.
  - exact Hs.
  - pose proof (classify_RegFix_char b p Hp) as Cp; unfold on_border in Cp.
    pose proof (classify_RegUp_char   b q Hq) as Cq. rewrite <- Hx in Cq. lra.
  - pose proof (classify_RegFix_char b p Hp) as Cp; unfold on_border in Cp.
    pose proof (classify_RegDown_char b q Hq) as Cq. rewrite <- Hx in Cq. lra.
  - pose proof (classify_RegUp_char   b p Hp) as Cp.
    pose proof (classify_RegFix_char b q Hq) as Cq; unfold on_border in Cq.
    rewrite <- Hx in Cq. lra.
  - lra.
  - pose proof (classify_RegUp_char   b p Hp) as Cp.
    pose proof (classify_RegDown_char b q Hq) as Cq. rewrite <- Hx in Cq. lra.
  - pose proof (classify_RegDown_char b p Hp) as Cp.
    pose proof (classify_RegFix_char b q Hq) as Cq; unfold on_border in Cq.
    rewrite <- Hx in Cq. lra.
  - pose proof (classify_RegDown_char b p Hp) as Cp.
    pose proof (classify_RegUp_char   b q Hq) as Cq. rewrite <- Hx in Cq. lra.
  - lra.
Qed.


(* 基本はセグメント全体を一定量だけ上下させる．                        *)
(* 境界線に接するセグメントは，自分の可変域の中だけで形を変える．       *)
Parameter operate_seg : list Segment -> list Segment -> R -> Segment -> Segment.

Definition operate_segs (ctx sub : list Segment) (h : R) (ls : list Segment)
  : list Segment := map (operate_seg ctx sub h) ls.

(* dzone を移動．集合を上下したもののほか，その集合に含まれ境界線上にあった線分と，
    上下移動した後のその線分からなる閉長方形を含む *)
Parameter operate_dzone : Point_Set -> R -> Point_Set.

(* 移動後の可変域は，簡約部分の長方形の内部には入らない *)
Axiom operate_dzone_avoids_rect :
  forall l sub r h i p,
    well_split l sub r -> h_large h sub ->
    operate_dzone (dzone (l ++ sub ++ r) sub i) h p ->
    ~ in_rect (rect_of sub) p.

(* --- operate_seg の仕様 --- *)

(* 仕様1：境界線上に完全に乗るセグメントは不動（簡約部分） *)
Axiom operate_seg_fix :
  forall ctx sub h s,
    (forall p, onSegment s p -> on_border (make_border ctx sub) p) ->
    operate_seg ctx sub h s = s.

(* 仕様2：移動後の点は「厳密な上下移動の像」か「移動後の可変域の中」。
   境界線と交わるセグメントは、端点を上下移動した後に
   operate_dzone (dzone ctx sub i) h の内部で調整される。 *)
Axiom operate_seg_zone : forall ctx sub h s i p, 
  nth_error ctx i = Some s ->
    onSegment (operate_seg ctx sub h s) p ->
      (exists p0, onSegment s p0
                  /\ p = operate_point (make_border ctx sub) h p0)
      \/ operate_dzone (dzone ctx sub i) h p.

Axiom operate_seg_zone_head : forall ctx sub h s i p, 
  nth_error ctx i = Some s ->
    onHead (operate_seg ctx sub h s) p ->
      (exists p0, onHead s p0
                  /\ p = operate_point (make_border ctx sub) h p0)
      \/ operate_dzone (dzone ctx sub i) h p.

Axiom operate_seg_zone_last : forall ctx sub h s i p, 
  nth_error ctx i = Some s ->
    onLast (operate_seg ctx sub h s) p ->
      (exists p0, onLast s p0
                  /\ p = operate_point (make_border ctx sub) h p0)
      \/ operate_dzone (dzone ctx sub i) h p.

(* TODO : 上3つとまとめる *)
Axiom operate_seg_zone_par : forall ctx sub h s i t,
  nth_error ctx i = Some s ->
  (exists t0,
      (t <= 0 -> t0 <= 0)
   /\ (0 < t <= 1 -> 0 < t0 <= 1)
   /\ (1 < t -> 1 < t0)
   /\ point (operate_seg ctx sub h s) t
      = operate_point (make_border ctx sub) h (point s t0))
  \/ operate_dzone (dzone ctx sub i) h
       (point (operate_seg ctx sub h s) t).

(* 仕様3 : 端点は「点だけで決まる写像」で動く。                              *)
(* 境界線上の端点は classify = RegFix なので不動、それ以外は ±h。      *)
(* いずれにせよ operate_point で書ける ＝ 端点の像はセグメントに依存しない *)
Axiom operate_seg_init : forall ctx sub h s,
  init (operate_seg ctx sub h s) = operate_point (make_border ctx sub) h (init s).
Axiom operate_seg_term : forall ctx sub h s,
  term (operate_seg ctx sub h s) = operate_point (make_border ctx sub) h (term s).
Lemma operate_segs_app :
  forall ctx sub h ls1 ls2,
    operate_segs ctx sub h (ls1 ++ ls2)
    = operate_segs ctx sub h ls1 ++ operate_segs ctx sub h ls2.
Proof. intros. unfold operate_segs. apply map_app. Qed.

(* ---- 長さの保存 ---------------------------------------- *)
Lemma operate_segs_length : forall ctx sub h ls,
  length (operate_segs ctx sub h ls) = length ls.
Proof. intros. unfold operate_segs. apply length_map. Qed.

(* 添字アクセスの可換性 *)
Lemma operate_segs_nth_error : forall ctx sub h ls i s,
  nth_error ls i = Some s ->
  nth_error (operate_segs ctx sub h ls) i = Some (operate_seg ctx sub h s).
Proof.
  intros ctx sub h ls i s H. unfold operate_segs.
  rewrite nth_error_map, H. reflexivity.
Qed.

Lemma operate_segs_nth : forall ctx sub h ls i,
  (i < length ls)%nat ->
  nth i (operate_segs ctx sub h ls) default_segment
  = operate_seg ctx sub h (nth i ls default_segment).
Proof.
  intros ctx sub h ls i Hi. unfold operate_segs.
  rewrite (nth_indep _ default_segment (operate_seg ctx sub h default_segment)).
  - apply map_nth.
  - rewrite length_map. exact Hi.
Qed.


Lemma at_pos_operate : forall ctx sub h q,
  (fst q < length ctx)%nat ->
  at_pos (operate_segs ctx sub h ctx) q
  = point (operate_seg ctx sub h (nth (fst q) ctx default_segment)) (snd q).
Proof.
  intros ctx sub h q Hi. unfold at_pos.
  rewrite (operate_segs_nth ctx sub h ctx (fst q) Hi). reflexivity.
Qed.

Lemma in_range_operate : forall ctx sub h q,
  in_range (operate_segs ctx sub h ctx) q <-> in_range ctx q.
Proof.
  intros. unfold in_range. rewrite operate_segs_length. reflexivity.
Qed.

(* 移動後の点は「元の点の operate_point 像」か「自分の移動後の可変域」 *)
Lemma trace_pos : forall ctx sub h q,
  in_range ctx q ->
  (exists t0, in_range ctx (fst q, t0)
      /\ at_pos (operate_segs ctx sub h ctx) q
         = operate_point (make_border ctx sub) h (at_pos ctx (fst q, t0)))
  \/ operate_dzone (dzone ctx sub (fst q)) h
       (at_pos (operate_segs ctx sub h ctx) q).
Proof.
  intros ctx sub h q Hr. pose proof Hr as [Hi [Hlo Hup]].
  rewrite (at_pos_operate ctx sub h q Hi).
  assert (Hnth : nth_error ctx (fst q) = Some (nth (fst q) ctx default_segment)). {
    apply nth_error_nth'.
    assumption.
  }
  destruct (operate_seg_zone_par ctx sub h
             (nth (fst q) ctx default_segment) (fst q) (snd q) Hnth)
    as [[t0 (Hn & Hm & Hp & Heq)] | Hz]; [| right; exact Hz].
  left. exists t0. split; [| unfold at_pos; simpl; exact Heq].
  unfold in_range; simpl. repeat split; [exact Hi | | ].
  - destruct Hlo as [H0 | H0]; [left; exact H0 | right].
    destruct (Rle_dec (snd q) 1) as [Hle | Hgt].
    + apply Hm; lra.
    + apply Rlt_trans with 1; [lra | apply Hp; lra].
  - destruct Hup as [H1 | H1]; [left; exact H1 | right].
    destruct (Rlt_dec 0 (snd q)) as [Hge | Hlt].
    + apply Hm; lra.
    + apply Rle_trans with 0; [apply Hn; lra | lra].
Qed.

(* 鉛直平行移動（向きの不変性を持つ） *)
(* TODO : これを用いて operate_seg を実装 *)
Parameter vshift_seg : R -> Segment -> Segment.

Axiom vshift_seg_point : forall d s t,
  point (vshift_seg d s) t = (fst (point s t), snd (point s t) + d).
Axiom orn_vshift : forall d s, orn_seg (vshift_seg d s) = orn_seg s.

Definition shift_amount (g : Region) (h : R) : R :=
  match g with RegFix => 0 | RegUp => h | RegDown => -h end.

(* 単一領域に収まるセグメントは「丸ごと鉛直平行移動」   *)
(*   これがあると operate_seg_zone の第1枝も等式から従う             *)
Definition seg_in_region (b : Border) (g : Region) (s : Segment) : Prop :=
  forall p, onSegment s p -> classify b p = g.

Axiom operate_seg_uniform :
  forall ctx sub h g s,
    seg_in_region (make_border ctx sub) g s ->
    operate_seg ctx sub h s = vshift_seg (shift_amount g h) s.

Lemma operate_seg_init_uniform : forall ctx sub h g s,
  seg_in_region (make_border ctx sub) g s ->
  init (operate_seg ctx sub h s)
  = operate_point (make_border ctx sub) h (init s).
Proof.
  intros ctx sub h g s Hg.
  rewrite (operate_seg_uniform ctx sub h g s Hg).
  unfold init. rewrite vshift_seg_point.
  unfold operate_point, shift.
  assert (Hcl : classify (make_border ctx sub) (init s) = g)
    by (apply Hg; unfold init; apply onInit).
  unfold init in Hcl; rewrite Hcl. 
  destruct g; unfold shift_amount; simpl; f_equal. 
  rewrite Rplus_0_r.
  destruct (point s 0); reflexivity.
Qed.

(* 単一領域の場合 *)
Lemma operate_seg_orn_uniform :
  forall ctx sub h g s,
    seg_in_region (make_border ctx sub) g s ->
    orn_seg (operate_seg ctx sub h s) = orn_seg s.
Proof.
  intros ctx sub h g s Hg.
  rewrite (operate_seg_uniform ctx sub h g s Hg). apply orn_vshift.
Qed.

(* 境界線を横断する場合 *)
(* 境界線と交わるセグメントは，可変域の中だけで形を変えて向きを保つ    *)
Lemma reconnect_one_segment :
  forall ctx sub h s,
    ~ weakly_above (make_border ctx sub) (onSegment s) ->
    ~ weakly_below (make_border ctx sub) (onSegment s) ->
    orn_seg (operate_seg ctx sub h s) = orn_seg s.
Admitted.

(* 移動後も可変域は私有：他のセグメントが入るなら隣接に限る *)
Lemma dzone_private : forall ctx sub h i j p,
  (i < length ctx)%nat -> (j < length ctx)%nat -> i <> j ->
  operate_dzone (dzone ctx sub i) h p ->
  onExtAt (operate_segs ctx sub h ctx) j p ->
  S i = j \/ S j = i.
Proof.
Admitted.

(* 隣接する操作後セグメントは、共有端点以外で交わらない。
   共有端点は位置 (i,1) としてのみ表され、(i+1,0) は in_range でないので、
   in_range な2位置が一致することはない。 *)
Axiom operate_adjacent_disjoint : forall ctx sub h q1 q2,
  S (fst q1) = fst q2 ->
  in_range (operate_segs ctx sub h ctx) q1 ->
  in_range (operate_segs ctx sub h ctx) q2 ->
  at_pos (operate_segs ctx sub h ctx) q1 <> at_pos (operate_segs ctx sub h ctx) q2.

(* セグメントと境界線の位置関係の場合分け（排中律 Classical が必要？）*)
(* TODO : make_border の性質 の節のものとまとめる *)
Lemma classify_cases : forall b s,
  (exists g, seg_in_region b g s)
  \/ (~ weakly_above b (onSegment s) /\ ~ weakly_below b (onSegment s)).
Admitted.

(* ---- 統合（場合分けを尽くす）--------------------------- *)
Lemma operate_seg_orn' : forall ctx sub h s,
  orn_seg (operate_seg ctx sub h s) = orn_seg s.
Proof.
  intros ctx sub h s.
  destruct (classify_cases (make_border ctx sub) s) as [[g Hg] | [Ha Hb]].
  - eapply operate_seg_orn_uniform; exact Hg.
  - apply (reconnect_one_segment ctx sub h s Ha Hb).
Qed.

(* ---- 仕様3：向きの保存 ----------------- *)
Lemma operate_segs_orn_map : forall ctx sub h ls,
  map orn_seg (operate_segs ctx sub h ls) = map orn_seg ls.
Proof.
  intros. unfold operate_segs. rewrite map_map.
  apply map_ext. intros s. apply operate_seg_orn'.
Qed.

Lemma operate_segs_orn_nth_error : forall ctx sub h ls i s s',
  nth_error ls i = Some s ->
  nth_error (operate_segs ctx sub h ls) i = Some s' ->
  orn_seg s' = orn_seg s.
Proof.
  intros ctx sub h ls i s s' Hs Hs'.
  rewrite (operate_segs_nth_error ctx sub h ls i s Hs) in Hs'.
  injection Hs' as Hs'. subst s'. apply operate_seg_orn'.
Qed.

(* 連結性の保存 *)
Lemma operate_segs_connected : forall ctx sub h ls,
  connected ls -> connected (operate_segs ctx sub h ls).
Proof.
  intros ctx sub h ls Hc n s1 s2 H1 H2.
  unfold operate_segs in H1, H2.
  destruct (nth_error_map_inv _ _ _ _ H1) as [a [Ha Ea]].
  destruct (nth_error_map_inv _ _ _ _ H2) as [b [Hb Eb]].
  subst s1 s2.
  rewrite operate_seg_term, operate_seg_init.
  f_equal. exact (Hc n a b Ha Hb).
Qed.


(* ================================================================= *)
(*  5.  移動先が長方形に入らないこと                                   *)
(* ================================================================= *)

(* 境界線と交わる点がどれも，簡約部分の長方形の外側にあるような点集合 P について，
    P の点 p0 を動かしたら，簡約部分の長方形の外側に行く *)
Lemma operate_pt_not_in_rect :
  forall l sub r h (P : Point_Set) p0,
    well_split l sub r -> h_large h sub ->
    (forall x, contact_x (border_of l sub r) P x -> outside_rect_x sub x) ->
    P p0 ->
    ~ in_rect (rect_of sub) (operate_point (border_of l sub r) h p0).
Proof.
  intros l sub r h P p0 Hws Hh Hct HP Hin.
  destruct Hws as [Hne [Hx Hop]].
  assert (Hws : well_split l sub r) by (split; [exact Hne | split; assumption]).
  destruct Hh as [Hh0 Hh].
  pose proof (rect_of_in_bbox sub Hne) as [Hb0 Hb1].
  unfold rect_height in Hh.
  unfold operate_point in Hin.
  destruct (classify (border_of l sub r) p0) eqn:Hg; unfold shift in Hin.

  - (* RegFix : 不動．境界線に触るので接触点 ⇒ x 範囲の外 ⇒ 矛盾 *)
    destruct Hin as [[Hx0 Hx1] _].
    assert (Hc : contact_x (border_of l sub r) P (fst p0)).
    { exists p0. repeat split;
      [exact HP | apply (classify_RegFix_char _ p0 Hg)]. }
    destruct (Hct _ Hc); unfold outside_rect_x in *; lra.

  - (* RegUp : 上へ h．b(x) は bbox の中 ＆ h > bbox の高さ ⇒ 矛盾 *)
    pose proof (classify_RegUp_char _ p0 Hg) as Hup.
    destruct Hin as [[Hx0 Hx1] [Hy0 Hy1]]. cbn [fst snd] in *.
    destruct (mb_cover l sub r Hws (fst p0)) as [q [Hq [Hqx Hqy]]]; [lra|].
    pose proof (bbox_of_bounds sub q Hq) as [Hql Hqr].
    lra.

  - (* RegDown : 下へ h．対称 *)
    pose proof (classify_RegDown_char _ p0 Hg) as Hdn.
    destruct Hin as [[Hx0 Hx1] [Hy0 Hy1]]. cbn [fst snd] in *.
    destruct (mb_cover l sub r Hws (fst p0)) as [q [Hq [Hqx Hqy]]]; [lra|].
    pose proof (bbox_of_bounds sub q Hq) as [Hql Hqr].
    lra.
Qed.

Lemma operate_segs_fix :
  forall l sub r h, well_split l sub r ->
    operate_segs (l ++ sub ++ r) sub h sub = sub.
Proof.
  intros l sub r h Hws. unfold operate_segs.
  apply map_id_pointwise. intros s Hs.
  apply operate_seg_fix. intros p Hp.
  apply (mb_fits l sub r Hws). exists s. split; assumption.
Qed.

Lemma operate_split :
  forall l sub r h, well_split l sub r ->
    operate_segs (l ++ sub ++ r) sub h (l ++ sub ++ r)
    = operate_segs (l ++ sub ++ r) sub h l
      ++ sub
      ++ operate_segs (l ++ sub ++ r) sub h r.
Proof.
  intros l sub r h Hws.
  rewrite !operate_segs_app, (operate_segs_fix l sub r h Hws). reflexivity.
Qed.

Lemma hd_operate :
  forall l sub r h, well_split l sub r ->
    hd_segment (operate_segs (l ++ sub ++ r) sub h l
                ++ sub
                ++ operate_segs (l ++ sub ++ r) sub h r)
    = operate_seg (l ++ sub ++ r) sub h (hd_segment (l ++ sub ++ r)).
Proof.
  intros l sub r h Hws. destruct Hws as [Hne Hdummy] eqn : E.
  destruct l as [|a l']; simpl.
  - destruct sub as [|s sub']; [contradiction|]. simpl.
    symmetry. apply operate_seg_fix. intros p Hp.
    apply (mb_fits [] (s :: sub') r). { assumption. }
    exists s. split; [left; reflexivity | exact Hp].
  - reflexivity.
Qed.

Lemma last_operate :
  forall l sub r h, well_split l sub r ->
    last_segment (operate_segs (l ++ sub ++ r) sub h l
                  ++ sub
                  ++ operate_segs (l ++ sub ++ r) sub h r)
    = operate_seg (l ++ sub ++ r) sub h (last_segment (l ++ sub ++ r)).
Proof.
  intros l sub r h Hws. pose proof Hws as Hws'. destruct Hws as [Hne _].
  destruct r as [|c r'].
  - rewrite !app_nil_r.
    rewrite !(last_app_nonnil _ _ Hne).
    symmetry. apply operate_seg_fix. intros p Hp.
    assert (H : l ++ sub = l ++ sub ++ []). {
      rewrite app_nil_r.
      reflexivity.
    } 
    rewrite H.
    apply (mb_fits l sub [] Hws').
    exists (last_segment sub). split; [| exact Hp].
    destruct sub as [|a tl]; [contradiction | apply last_In].
    assumption.
  - assert (Hnc : operate_segs (l ++ sub ++ c :: r') sub h (c :: r') <> [])
      by (unfold operate_segs; simpl; discriminate).
    assert (Hcr : c :: r' <> []) by discriminate.
    rewrite (app_assoc (operate_segs _ _ _ _) sub (operate_segs _ _ _ _)).
    rewrite (last_app_nonnil _ _ Hnc). 
    rewrite (app_assoc l sub (c :: r')). 
    rewrite (last_app_nonnil _ _ Hcr).
    unfold operate_segs. rewrite last_map_cons. reflexivity.
Qed.


(* ================================================================= *)
(*  6.  核となる補題                                            *)
(* ================================================================= *)

(* ---- Lemma A : 埋め込みの保存 ----------------------------------- *)
(* 向きが変わらないことと，連結性が保存されることから *)
Lemma operate_preserves_embed : forall ctx sub h ds ls,
  embed_listDir ds ls -> embed_listDir ds (operate_segs ctx sub h ls).
Proof.
  intros ctx sub h ds ls Hemb.
  eapply embed_scurve_transfer; [exact Hemb | | |].
  - apply operate_segs_length.
  - intros i s s' Hs Hs'. eapply operate_segs_orn_nth_error; eauto.
  - apply operate_segs_connected. eapply embed_listDir_connected; exact Hemb.
Qed.

(* ---- Lemma B : 開の保存 ----------------------------------------- *)
(*  [1] セグメント×セグメント：同領域なら同じ h 平行移動 ⇒ 移動前も    *)
(*      交差して矛盾／可変域に入る場合は dz_local より隣接 ⇒       *)
(*      共有端点であって自己交差ではない                              *)
(*  [2] セグメント×延長線，[3] 延長線×延長線：同様に帰着              *)
Lemma operate_preserves_open : forall l sub r h,
  well_split l sub r -> 0 < h -> 
  ~ close (operate_segs (l ++ sub ++ r) sub h l
           ++ sub
           ++ operate_segs (l ++ sub ++ r) sub h r).
Proof.
  intros l sub r h Hws Hh Hcl.
  pose proof Hws as Hws'. destruct Hws' as [Hne [Hxm Hopen]].

  (* 3分割を1本の map に戻す：以降 ctx' = operate_segs ctx sub h ctx *)
  rewrite <- (operate_split l sub r h Hws) in Hcl.
  set (ctx := l ++ sub ++ r) in *.

  assert (Hnonnil :operate_segs ctx sub h ctx <> []). {
      intros contra.
      pose proof (operate_segs_length ctx sub h ctx) as H.
      rewrite contra in H. 
      subst ctx.
      simpl in H.
      symmetry in H.
      apply length_zero_iff_nil in H.
      apply app_eq_nil in H as [_ H].
      apply app_eq_nil in H as [H _].
      contradiction.
    }
  apply close_crossing in Hcl; try assumption.
  destruct Hcl as (q1 & q2 & Hr1 & Hr2 & Heq & Hq12).
  pose proof (proj1 (in_range_operate ctx sub h q1) Hr1) as Hc1.
  pose proof (proj1 (in_range_operate ctx sub h q2) Hr2) as Hc2.
  destruct Hc1 as [Hi1 Hdummy1] eqn:E1. destruct Hc2 as [Hi2 Hdummy2] eqn:E2.

  (* ---- ケース1：同一セグメント内 ⇒ point_injective ---- *)
  destruct (Nat.eq_dec (fst q1) (fst q2)) as [Hsame | Hdiff].
  { rewrite (at_pos_operate ctx sub h q1 Hi1),
            (at_pos_operate ctx sub h q2 Hi2), Hsame in Heq.
    apply point_injective in Heq.
    apply Hq12. destruct q1, q2; simpl in *; congruence. }

  (* ---- ケース2：隣接セグメント ⇒ 共有端点なので junction ---- *)
  destruct (Nat.eq_dec (S (fst q1)) (fst q2)) as [Ha1 | Ha1].
  { eapply operate_adjacent_disjoint; eassumption. }
  destruct (Nat.eq_dec (S (fst q2)) (fst q1)) as [Ha2 | Ha2].
  { eapply operate_adjacent_disjoint; try eassumption.
    symmetry; assumption. }

  (* ---- ケース3：非隣接かつ異なるセグメント ---- *)
  destruct (trace_pos ctx sub h q1 Hc1) as [[t1 [Hin1 Heq1]] | Hz1].
  2:{ (* q1 が可変域 ⇒ dzone_private より隣接、矛盾 *)
      destruct (dzone_private ctx sub h (fst q1) (fst q2) _ Hi1 Hi2 Hdiff Hz1)
        as [H|H]; [ | contradiction | contradiction].
      Unshelve. exists (snd q2). split; [exact Hr2 |].
      destruct q2; simpl; rewrite <- Heq; reflexivity. }
  destruct (trace_pos ctx sub h q2 Hc2) as [[t2 [Hin2 Heq2]] | Hz2].
  2:{ destruct (dzone_private ctx sub h (fst q2) (fst q1) _ Hi2 Hi1
                 (not_eq_sym Hdiff) Hz2) as [H|H]; [ | contradiction|contradiction].
      Unshelve. exists (snd q1). split; [exact Hr1 |].
      destruct q1; simpl; rewrite Heq; reflexivity. }

  (* 両方が厳密な平行移動 ⇒ operate_point_inj で元の点も一致 ⇒ 元の曲線が交差 *)
  rewrite Heq1, Heq2 in Heq.
  apply (operate_point_inj (make_border ctx sub) h _ _ Hh) in Heq.
    apply Hopen. apply crossing_close; [exact (open_nonnil _ Hopen) |].
  exists (fst q1, t1), (fst q2, t2). 
  assert (Hnepair : (fst q1, t1) <> (fst q2, t2)).
  { intros Hcon. apply Hdiff.
    apply (f_equal fst) in Hcon. simpl in Hcon. exact Hcon. }
  split; [exact Hin1 |].
  split; [exact Hin2 |].
  split; [exact Heq | exact Hnepair].
Qed.

(* ---- Lemma C : 移動すると疎になる ------------------ *)
Lemma operate_gives_sparse :
  forall l sub r h, well_split l sub r -> h_large h sub ->
    sparse (operate_segs (l ++ sub ++ r) sub h l)
           sub
           (operate_segs (l ++ sub ++ r) sub h r).
Proof.
  intros l sub r h Hws Hh. pose proof Hws as Hws'. destruct Hws' as [Hne _].
  unfold sparse. intros p H.
  destruct H as [Hhead | [Hmid | Hlast]].

  - (* [head] 先頭の延長線 *)
    unfold onHead_extend in Hhead.
    rewrite (hd_operate l sub r h Hws) in Hhead.
    assert (Hin : nth_error (l ++ sub ++ r) 0 = Some (hd_segment (l ++ sub ++ r))).
    { destruct l as [|a l']; simpl;
      [destruct sub as [|s sub']; [contradiction | reflexivity]
      | reflexivity ]. }
    destruct (operate_seg_zone_head _ sub h _ 0 p Hin Hhead)
      as [[p0 [Hp0 Heq]] | Hz].
    + subst p. eapply (operate_pt_not_in_rect l sub r h
                         (onHead_extend (l ++ sub ++ r))); eauto.
      apply (mb_ct_head l sub r Hws).
    + eapply (operate_dzone_avoids_rect l sub r h 0 p Hws Hh Hz).

  - (* [mid] l, r のセグメント *)
    destruct Hmid as [s [Hs Hp]].
    assert (Hs0 : exists s0, In s0 (l ++ r)
                             /\ s = operate_seg (l ++ sub ++ r) sub h s0).
    { apply in_app_or in Hs; destruct Hs as [H|H]; unfold operate_segs in H;
      apply in_map_iff in H; destruct H as [s0 [Heq Hin]];
      exists s0; split; try congruence; apply in_or_app; auto. }
    destruct Hs0 as [s0 [Hin0 Heq0]]. subst s.
    assert (Hinctx : In s0 (l ++ sub ++ r)).
    { apply in_app_or in Hin0. destruct Hin0 as [H|H]; apply in_or_app;
      [left; exact H | right; apply in_or_app; right; exact H]. }
    assert (Hi : exists i, nth_error (l ++ sub ++ r) i = Some s0).
    { apply In_nth_error. exact Hinctx. }
    destruct Hi as [i Hi].
    destruct (operate_seg_zone _ sub h s0 i p Hi Hp)
      as [[p0 [Hp0 Heq]] | Hz].
    + subst p. eapply (operate_pt_not_in_rect l sub r h
                         (onSegmentlist (l ++ r))); eauto.
      * apply (mb_ct_seg l sub r Hws).
      * exists s0. split; assumption.
    + eapply (operate_dzone_avoids_rect l sub r h i p Hws Hh Hz).

  - (* [last] 末尾の延長線 *)
    unfold onLast_extend in Hlast.
    rewrite (last_operate l sub r h Hws) in Hlast.
    assert (Hnonnil :l ++ sub ++ r <> []). {
      intros H.
      apply app_eq_nil in H as [_ H].
      apply app_eq_nil in H as [H _].
      contradiction.
    }
    assert (Hin : In (last_segment (l ++ sub ++ r)) (l ++ sub ++ r)).
    { destruct (l ++ sub ++ r) as [|a tl] eqn:E.
      - destruct l; destruct sub; simpl in E; try discriminate; contradiction.
      - rewrite <- E. rewrite E. apply last_In. assumption. }
    assert (Hi : exists i, nth_error (l ++ sub ++ r) i
                           = Some (last_segment (l ++ sub ++ r))).
    { apply In_nth_error. exact Hin. }
    destruct Hi as [i Hi].
    destruct (operate_seg_zone_last _ sub h _ i p Hi Hlast)
      as [[p0 [Hp0 Heq]] | Hz].
    + subst p. eapply (operate_pt_not_in_rect l sub r h
                         (onLast_extend (l ++ sub ++ r))); eauto.
      apply (mb_ct_last l sub r Hws).
    + eapply (operate_dzone_avoids_rect l sub r h i p Hws Hh Hz).
Qed.



(* ================================================================= *)
(*  7.  最終命題                          *)
(* ================================================================= *)

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
   /\ sparse l' sub' r'
   /\ sub' <> []. 
Proof.
  intros ds1 sub_ds ds2 l sub r Hl Hsub Hr Hall Hws.
  pose proof Hws as Hws'. destruct Hws' as [Hne _].
  destruct (choose_h sub) as [h Hh].
  set (ctx := l ++ sub ++ r).
  exists (operate_segs ctx sub h l), (operate_segs ctx sub h r), sub.
  repeat split.
  - eapply operate_preserves_embed; exact Hl.
  - exact Hsub.
  - eapply operate_preserves_embed; exact Hr.
  - subst ctx. rewrite <- (operate_split l sub r h Hws).
    eapply operate_preserves_embed; exact Hall.
  - subst ctx. eapply operate_preserves_open;
    [ exact Hws | apply (proj1 Hh) ].
  - subst ctx. eapply operate_gives_sparse; eauto.
  - exact Hne.
Qed.

Proposition embed_sparsely_listDir (ds1 sub_ds ds2 : list Direction) :
  AdmissibleDirs (ds1 ++ sub_ds ++ ds2)
  -> is_one_way_listDir sub_ds
  -> exists l r sub_ls,
       embed_listDir ds1 l
    /\ embed_listDir sub_ds sub_ls
    /\ embed_listDir ds2 r
    /\ embed_listDir (ds1 ++ sub_ds ++ ds2) (l ++ sub_ls ++ r)
    /\ ~ close (l ++ sub_ls ++ r)
    /\ sparse l sub_ls r.
Proof.
  intros Hadm Hone.

  (* Step 1 : 開埋め込みを1つ得る *)
  destruct (admissible_gives_open_embed _ Hadm) as [ls0 [Hemb0 Hopen0]].

  (* Step 2 : 3 分割 *)
  destruct (embed_split _ _ _ _ Hemb0)
    as (l0 & sub0 & r0 & Heq & Hl0 & Hsub0 & Hr0).
  subst ls0.

  (* Step 3 : 非空性 *)
  assert (Hne : sub0 <> []).
  { eapply embed_nonnil; [exact Hsub0 | apply one_way_listDir_nonnil; exact Hone]. }

  (* Step 4 : sub0 は単方向 *)
  assert (Honeway : is_one_way_embedding sub0).
  { destruct Hsub0 as [sc [Hdir Hembed]]. exists sc. split; [exact Hembed|].
    destruct Hone as [sc' [Hdir' Honeway]].
    apply (is_one_way_same_direction _ _ (eq_trans Hdir' (eq_sym Hdir)) Honeway). }

  (* Step 5 : 回転して x 正方向単調にし，疎な埋め込みを取る *)
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
           | split; [ exact Hx
                    | rewrite <- !rot_segs_app; apply rot_open; exact Hopen0 ]]. }

  exists L, Rr, S.
  repeat split; assumption.
Qed.
