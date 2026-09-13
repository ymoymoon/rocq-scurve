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



(* ================================================================= *)
(*  0.  基本プリミティブ                                              *)
(* ================================================================= *)

Definition rightabove (rr1 rr2 : Point) :=
  let (x1, y1) := rr1 in
  let (x2, y2) := rr2 in x1 < x2 /\ y1 < y2.
Definition rightbelow (rr1 rr2 : Point) :=
  let (x1, y1) := rr1 in
  let (x2, y2) := rr2 in x1 < x2 /\ y2 < y1.

Definition connected (ls : list Segment) : Prop :=
  forall i s1 s2, nth_error ls i = Some s1 -> nth_error ls (S i) = Some s2 ->
    term s1 = init s2.

(* 連結な列の連続部分列は連結である。 *)
Lemma connected_middle :
  forall l sub r,
    connected (l ++ sub ++ r) -> connected sub.
Proof.
  intros l sub r Hconn i s1 s2 H1 H2.
  apply (Hconn (length l + i)%nat s1 s2).
  - change (nth_error (l ++ (sub ++ r)) (length l + i) = Some s1).
    assert (Hle : (length l <= length l + i)%nat) by lia.
    rewrite (nth_error_app2 l (sub ++ r) Hle).
    replace (length l + i - length l)%nat with i by lia.
    rewrite nth_error_app1; [exact H1 |].
    apply nth_error_Some. rewrite H1. discriminate.
  - replace (S (length l + i)) with (length l + S i)%nat by lia.
    change (nth_error (l ++ (sub ++ r)) (length l + S i) = Some s2).
    assert (Hle : (length l <= length l + S i)%nat) by lia.
    rewrite (nth_error_app2 l (sub ++ r) Hle).
    replace (length l + S i - length l)%nat with (S i) by lia.
    rewrite nth_error_app1; [exact H2 |].
    apply nth_error_Some. rewrite H2. discriminate.
Qed.

Definition onSegment' (seg: Segment) (rr : R * R) := exists (t:R), 0 < t <= 1 /\ point seg t = rr.
(* TODO: 空リストを省く *)
Definition onSegmentlist l rr := exists seg, In seg l /\ onSegment seg rr.
(* TODO: extend に関する公理を完成させた後， onExtendSegment と整合することを確認
		特に空リストの扱い *)
Definition onExtend ls rr := exists t, rr = extend ls t.

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

(* 同じ長さの接頭辞を持つ二つの連結表示は、それぞれの部分が一致する。 *)
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

(* リストの [i] 番目を抜き出した前後の文脈。別の位置の要素は必ず外側に残る。 *)
Lemma nth_error_other_context :
  forall (ls : list Segment) (i j : nat) (s t : Segment),
    nth_error ls i = Some s ->
    nth_error ls j = Some t ->
    i <> j ->
    exists l r, ls = l ++ [s] ++ r /\ In t (l ++ r).
Proof.
  induction ls as [|a ls IH]; intros i j s t Hi Hj Hneq.
  - destruct i; simpl in Hi; discriminate.
  - destruct i as [|i], j as [|j]; simpl in Hi, Hj.
    + exfalso. apply Hneq. reflexivity.
    + injection Hi as Hs. subst s.
      exists [], ls. split; [reflexivity|].
      now apply nth_error_In in Hj.
    + injection Hj as Ht. subst t.
      apply nth_error_In in Hi.
      apply in_split in Hi as [l [r Hls]].
      exists (a :: l), r. split.
      * simpl. now rewrite Hls.
      * simpl. now left.
    + destruct (IH i j s t Hi Hj ltac:(lia)) as [l [r [Hls Hin]]].
      exists (a :: l), r. split.
      * simpl. now rewrite Hls.
      * simpl. now right.
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

(* scurve の埋め込みを任意の位置で、向き列とセグメント列を揃えて分割する。 *)
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


(* scurve の向き列と PrimitiveSegment 列の長さは一致する。 *)
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

(*  (orn_seg としての)向き列が同じで、長さが同じで、連結なら、同じ ds の埋め込み」 *)
Lemma embed_scurve_transfer : forall ds ls ls',
  embed_listDir ds ls ->
  length ls' = length ls ->
  (forall i s s', nth_error ls i = Some s -> nth_error ls' i = Some s' ->
                  orn_seg s' = orn_seg s) ->
  connected ls' ->
  embed_listDir ds ls'.
Admitted.

(* ---- 連結性は埋め込みから出る（Embed.v の consist_init_term）---- *)
Lemma embed_scurve_connected : forall sc ls,
  embed_scurve sc ls -> connected ls.
Proof.
  intros sc ls Hembed.
  induction Hembed as [
    | ps s Hembed_ps
    | ps lp A s1 s2 ls Hembed_ps Hembed_tail Hterm IH].
  - unfold connected. intros i s1 s2 H1 H2.
    rewrite nth_error_nil in H1. discriminate H1.
  - unfold connected. intros i s1 s2 H1 H2.
    destruct i; simpl in H2; discriminate H2.
  - unfold connected in IH |- *. intros i x y Hx Hy.
    destruct i as [|i].
    + simpl in Hx, Hy. inversion Hx; inversion Hy; subst. exact IH.
    + simpl in Hx, Hy. now apply (Hterm i x y Hx Hy).
Qed.

Lemma embed_listDir_connected : forall ds ls, embed_listDir ds ls -> connected ls.
Proof.
  intros ds ls [sc [_ Hembed]].
  now apply (embed_scurve_connected sc ls).
Qed.



(* ================================================================= *)
(*  1．AdmissibleDirs について成り立ってほしい性質と，それに必要な補題    *)
(* ================================================================= *)

Lemma Rmin_opp : forall a b, Rmin (- a) (- b) = - Rmax a b.
Proof. intros. unfold Rmin, Rmax. destruct (Rle_dec (-a) (-b)), (Rle_dec a b); lra. Qed.
Lemma Rmax_opp : forall a b, Rmax (- a) (- b) = - Rmin a b.
Proof. intros. unfold Rmin, Rmax. destruct (Rle_dec (-a) (-b)), (Rle_dec a b); lra. Qed.

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
(*  2.  長方形と sparse                                               *)
(* ================================================================= *)

(* 部分列の始点と終点を対角線にもつ長方形。
   1セグメントの長方形には rect_of [s] を用いる。 *)
Definition rect_of (sub : list Segment) : Rect :=
  let q0 := init (hd_segment sub) in
  let q3 := term (last_segment sub) in
  mkRect (Rmin (fst q0) (fst q3)) (Rmin (snd q0) (snd q3))
         (Rmax (fst q0) (fst q3)) (Rmax (snd q0) (snd q3)).

Definition rect_width  (Rc : Rect) : R := rx1 Rc - rx0 Rc.
Definition rect_height (Rc : Rect) : R := ry1 Rc - ry0 Rc.

(* 点が old の両端点、または old の開長方形の内部にある。 *)
Definition in_rect_or_endpoints_at (old : list Segment) (p : Point) : Prop :=
  p = init (hd_segment old)
  \/ p = term (last_segment old)
  \/ in_rect (rect_of old) p.

Definition in_segment_rect_or_endpoints (s : Segment) (p : Point) : Prop :=
  p = init s \/ p = term s \/ in_rect (rect_of [s]) p.

(* new の全ての点が old の両端点、または開長方形の内部にある。 *)
Definition in_rect_or_endpoints (old new : list Segment) : Prop :=
  forall p, onSegmentlist new p ->
    in_rect_or_endpoints_at old p.

(* [Segment.v] の基本契約を、このファイルの [Rect] 表現へ読み替える。 *)
Lemma segment_in_rect_or_endpoints :
  forall s p, onSegment s p -> in_segment_rect_or_endpoints s p.
Proof.
  intros s p Hp.
  destruct (segment_in_rectangle_or_endpoints s p Hp) as [Hinit | [Hterm | Hinside]].
  - now left.
  - now right; left.
  - right; right.
    unfold in_open_segment_rectangle, in_rect, rect_between in Hinside.
    unfold in_rect, rect_of; simpl in *.
    exact Hinside.
Qed.

Lemma single_segment_in_rect_or_endpoints :
  forall s, in_rect_or_endpoints [s] [s].
Proof.
  intros s p [t [Ht Hp]]. simpl in Ht.
  destruct Ht as [Ht | Hfalse]; [subst t | contradiction].
  change (in_segment_rect_or_endpoints s p).
  now apply segment_in_rect_or_endpoints.
Qed.

Lemma in_rect_implies_or_endpoints : forall old new,
  (forall p, onSegmentlist new p -> in_rect (rect_of old) p) ->
  in_rect_or_endpoints old new.
Proof. intros old new H p Hp. right; right; auto. Qed.

(* 全体の始点・終点そのものを除いた両端延長線。 *)
Definition onHead_extend_strict (ls : list Segment) (p : Point) : Prop :=
  exists t, t < 0 /\ point (hd_segment ls) t = p.

Definition onLast_extend_strict (ls : list Segment) (p : Point) : Prop :=
  exists t, 1 < t /\ point (last_segment ls) t = p.

(* sub と隣接する最後の l と先頭の r を除いた外側セグメント。 *)
Definition nonadjacent_sides (l r : list Segment) : list Segment :=
  removelast l ++ tl r.

Lemma nonadjacent_sides_map : forall (f : Segment -> Segment) l r,
  nonadjacent_sides (map f l) (map f r) = map f (nonadjacent_sides l r).
Proof.
  intros f l r. unfold nonadjacent_sides. rewrite map_app.
  assert (Hremove : removelast (map f l) = map f (removelast l)).
  { induction l using rev_ind; [reflexivity|].
    rewrite map_app. simpl. rewrite !removelast_last. reflexivity. }
  rewrite Hremove. destruct r; reflexivity.
Qed.

Lemma in_removelast_in : forall (A : Type) (x : A) xs,
  In x (removelast xs) -> In x xs.
Proof.
  intros A x xs. induction xs as [|a xs IH]; simpl; intros H; [contradiction|].
  destruct xs as [|b xs]; simpl in H |- *; [contradiction|].
  destruct H as [<- | H]; [now left | right; now apply IH].
Qed.

Lemma nonadjacent_sides_extend_right : forall l middle r s,
  In s (nonadjacent_sides l r) ->
  In s (nonadjacent_sides l (middle ++ r)).
Proof.
  intros l middle r s. unfold nonadjacent_sides.
  rewrite !in_app_iff. intros [Hl | Hr]; [now left | right].
  destruct middle as [|a middle]; [exact Hr |].
  simpl. rewrite in_app_iff. right.
  destruct r as [|b r]; simpl in Hr |- *; [contradiction | now right].
Qed.

Lemma nonadjacent_sides_extend_left : forall l middle r s,
  In s (nonadjacent_sides l r) ->
  In s (nonadjacent_sides (l ++ middle) r).
Proof.
  intros l middle r s. unfold nonadjacent_sides.
  rewrite !in_app_iff. intros [Hl | Hr]; [left | now right].
  destruct middle as [|a middle]; [now rewrite app_nil_r |].
  rewrite removelast_app by discriminate.
  rewrite in_app_iff. left. now apply in_removelast_in.
Qed.

(* p が strict 延長線または sub と非隣接の外側セグメントから来る。 *)
Definition outside_sub (l sub r : list Segment) (p : Point) : Prop :=
  let ls := l ++ sub ++ r in
  onHead_extend_strict ls p
  \/ onSegmentlist (nonadjacent_sides l r) p
  \/ onLast_extend_strict ls p.

(* strict 延長線と非隣接セグメントは、sub の開長方形と両端点を避ける。
   隣接セグメントと sub の共有端点は、埋め込みの連結性側で扱う。 *)
Definition sparse_around (l sub r : list Segment) : Prop :=
  (forall p,
     (onHead_extend_strict (l ++ sub ++ r) p
      \/ onLast_extend_strict (l ++ sub ++ r) p) ->
     ~ in_rect_or_endpoints_at sub p)
  /\ (forall s p,
        In s (nonadjacent_sides l r) ->
        in_segment_rect_or_endpoints s p ->
        ~ in_rect_or_endpoints_at sub p).

(* [outside_sub] の三つの場合を [sparse_around] からまとめて取り出す。 *)
Lemma sparse_around_outside_avoids : forall l sub r p,
  sparse_around l sub r ->
  outside_sub l sub r p ->
  ~ in_rect_or_endpoints_at sub p.
Proof.
  intros l sub r p [Hextend Hrect] Houtside.
  unfold outside_sub in Houtside.
  destruct Houtside as [Hhead | [Hsides | Hlast]].
  - now apply Hextend; left.
  - destruct Hsides as [s [Hs Hson]].
    apply (Hrect s p Hs).
    now apply segment_in_rect_or_endpoints.
  - now apply Hextend; right.
Qed.

(* ls の各セグメント出現の長方形について疎である。
   値が等しいセグメントが複数あっても、リスト中の位置を区別する。 *)
Definition sparse_embedding (ls : list Segment) : Prop :=
  forall l s r,
    ls = l ++ [s] ++ r ->
    sparse_around l [s] r.

(* 全域で疎であり、さらに指定した部分列 sub の周りでも疎である。 *)
Definition sparse (l sub r : list Segment) : Prop :=
  let ls := l ++ sub ++ r in
  sparse_embedding ls /\ sparse_around l sub r.

Lemma sparse_outside_avoids : forall l sub r p,
  sparse l sub r ->
  outside_sub l sub r p ->
  ~ in_rect (rect_of sub) p.
Proof.
  intros l sub r p [_ Haround] Houtside Hin.
  apply (sparse_around_outside_avoids l sub r p Haround Houtside).
  now right; right.
Qed.

(* 各セグメントに対し、非隣接セグメントの端点長方形を分離する。 *)
Definition segment_rectangles_separated (ls : list Segment) : Prop :=
  forall l s r,
    ls = l ++ [s] ++ r ->
    forall t, In t (nonadjacent_sides l r) ->
    forall p,
      in_segment_rect_or_endpoints t p ->
      ~ in_rect_or_endpoints_at [s] p.

Definition extensions_avoid_segment_rectangles (ls : list Segment) : Prop :=
  forall l s r,
    ls = l ++ [s] ++ r ->
    forall p,
      (onHead_extend_strict ls p \/ onLast_extend_strict ls p) ->
      ~ in_rect_or_endpoints_at [s] p.

(* 矩形・延長線・端点についての局所的な分離条件から全域疎性を組み立てる。 *)
Lemma geometric_sparse_embedding :
  forall ls,
    segment_rectangles_separated ls ->
    extensions_avoid_segment_rectangles ls ->
    sparse_embedding ls.
Proof.
  intros ls Hrect Hext l s r Heq.
  split.
  - intros p [Hhead | Hlast].
    + apply (Hext l s r Heq p). left. rewrite Heq. exact Hhead.
    + apply (Hext l s r Heq p). right. rewrite Heq. exact Hlast.
  - intros t p Ht Hp. eapply Hrect; eauto.
Qed.

(* 先頭延長線と末尾延長線が互いに交わらない。 ls が単一セグメントならば使わない？ *)
Definition extensions_disjoint (ls : list Segment) : Prop :=
  forall p,
    onHead_extend ls p ->
    onLast_extend ls p ->
    False.

(* 延長線の形や傾きそのものではなく、再接続後に必要となる安全性だけを
   まとめた述語。 *)
Definition extensions_safe (ls : list Segment) : Prop :=
  extensions_avoid_segment_rectangles ls /\ extensions_disjoint ls.

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

(* 埋め込まれた各セグメントは、自身の両端点または開長方形内にある。 *)
Lemma embedded_segments_in_rect_or_endpoints :
  forall ds ls,
    embed_listDir ds ls ->
    forall s, In s ls -> in_rect_or_endpoints [s] [s].
Proof. intros ds ls _ s _. apply single_segment_in_rect_or_endpoints. Qed.

Lemma extend_head_from_repr : forall ls t s,
  ls <> [] ->
  nth_error ls (extend_index ls t) = Some s ->
  extend ls t = point s (extend_param ls t) ->
  extend_index ls t = 0%nat ->
  extend_param ls t <= 0 ->
  onHead_extend ls (extend ls t).
Proof.
  intros ls t s Hne Hnth Hrepr Hindex Hparam.
  assert (Hs : hd_segment ls = s).
  { destruct ls as [|a ls]; [contradiction|].
    unfold hd_segment. simpl.
    rewrite Hindex in Hnth. simpl in Hnth. now injection Hnth. }
  unfold onHead_extend, onHead. exists (extend_param ls t).
  split; [exact Hparam|]. now rewrite Hs, <- Hrepr.
Qed.

Lemma extend_last_from_repr : forall ls t s,
  ls <> [] ->
  nth_error ls (extend_index ls t) = Some s ->
  extend ls t = point s (extend_param ls t) ->
  S (extend_index ls t) = length ls ->
  1 < extend_param ls t ->
  onLast_extend ls (extend ls t).
Proof.
  intros ls t s Hne Hnth Hrepr Hindex Hparam.
  assert (Hs : s = last_segment ls).
  { unfold last_segment.
    assert (K : extend_index ls t = (length ls - 1)%nat) by lia.
    rewrite K in Hnth.
    pose proof (@nth_error_last Segment ls default_segment Hne) as Hlast.
    rewrite Hnth in Hlast. now injection Hlast. }
  unfold onLast_extend, onLast. exists (extend_param ls t).
  split; [lra|]. now rewrite <- Hs, <- Hrepr.
Qed.

Lemma same_extend_piece_no_collision : forall ls t1 t2 s1 s2,
  ls <> [] ->
  nth_error ls (extend_index ls t1) = Some s1 ->
  nth_error ls (extend_index ls t2) = Some s2 ->
  extend_index ls t1 = extend_index ls t2 ->
  point s1 (extend_param ls t1) = point s2 (extend_param ls t2) ->
  t1 = t2.
Proof.
  intros ls t1 t2 s1 s2 Hne Hnth1 Hnth2 Hindex Heq.
  assert (Hs : s1 = s2).
  { rewrite <- (nth_error_nth_eq ls (extend_index ls t1) s1 default_segment Hnth1).
    rewrite Hindex.
    now rewrite (nth_error_nth_eq ls (extend_index ls t2) s2 default_segment Hnth2). }
  subst s2.
  apply (extend_same_piece_injective ls t1 t2); [exact Hne | exact Hindex |].
  now apply (point_injective s1).
Qed.

Lemma on_segment_term_from_x : forall s p,
  onSegment s p -> fst p = fst (term s) -> p = term s.
Proof.
  intros s p Hp Hx.
  destruct (segment_in_rect_or_endpoints s p Hp)
    as [Hinit | [Hterm | Hinside]].
  - subst p. exfalso. apply (neq_init_term_x s). exact Hx.
  - exact Hterm.
  - unfold in_segment_rect_or_endpoints, in_rect, rect_of in Hinside.
    simpl in Hinside. destruct Hinside as [[Hmin Hmax] _].
    rewrite Hx in Hmin, Hmax.
    destruct (Rle_dec (fst (init s)) (fst (term s))) as [Hle | Hgt].
    + rewrite Rmin_left in Hmin by exact Hle.
      rewrite Rmax_right in Hmax by exact Hle.
      exfalso. exact (Rlt_irrefl _ Hmax).
    + assert (Hrev : fst (term s) <= fst (init s)).
      { apply Rlt_le. now apply Rnot_le_lt. }
      rewrite Rmin_right in Hmin by exact Hrev.
      rewrite Rmax_left in Hmax by exact Hrev.
      exfalso. exact (Rlt_irrefl _ Hmin).
Qed.

Lemma on_segment_term_from_y : forall s p,
  onSegment s p -> snd p = snd (term s) -> p = term s.
Proof.
  intros s p Hp Hy.
  destruct (segment_in_rect_or_endpoints s p Hp)
    as [Hinit | [Hterm | Hinside]].
  - subst p. exfalso. apply (neq_init_term_y s). exact Hy.
  - exact Hterm.
  - unfold in_segment_rect_or_endpoints, in_rect, rect_of in Hinside.
    simpl in Hinside. destruct Hinside as [_ [Hmin Hmax]].
    rewrite Hy in Hmin, Hmax.
    destruct (Rle_dec (snd (init s)) (snd (term s))) as [Hle | Hgt].
    + rewrite Rmin_left in Hmin by exact Hle.
      rewrite Rmax_right in Hmax by exact Hle.
      exfalso. exact (Rlt_irrefl _ Hmax).
    + assert (Hrev : snd (term s) <= snd (init s)).
      { apply Rlt_le. now apply Rnot_le_lt. }
      rewrite Rmin_right in Hmin by exact Hrev.
      rewrite Rmax_left in Hmax by exact Hrev.
      exfalso. exact (Rlt_irrefl _ Hmin).
Qed.

(* 直接連結された二セグメントは共有端点以外では交わらない。 *)
Lemma adjacent_not_intersect_except_junction :
  forall ps1 ps2 s1 s2 p,
    dc ps1 ps2 ->
    embed ps1 s1 ->
    embed ps2 s2 ->
    term s1 = init s2 ->
    onSegment s1 p ->
    onSegment s2 p ->
    p = term s1.
Proof.
  intros ps1 ps2 s1 s2 [x y] Hdc Hembed1 Hembed2 Hjoin Hp1 Hp2.
  pose proof (f_equal fst Hjoin) as Hjoinx.
  pose proof (f_equal snd Hjoin) as Hjoiny.
  destruct Hdc as [v h c | h | h | h | h].
  - destruct h.
    + pose proof (e_onseg_relation s1 v c x y Hembed1 Hp1) as [_ Hx1].
      pose proof (e_onseg_relation s2 v (i_c c) x y Hembed2 Hp2) as [Hx2 _].
      apply on_segment_term_from_x; [exact Hp1 |]. simpl.
      apply Rle_antisym; [exact Hx1 | now rewrite Hjoinx].
    + pose proof (w_onseg_relation s1 v c x y Hembed1 Hp1) as [Hx1 _].
      pose proof (w_onseg_relation s2 v (i_c c) x y Hembed2 Hp2) as [_ Hx2].
      apply on_segment_term_from_x; [exact Hp1 |]. simpl.
      apply Rle_antisym; [now rewrite Hjoinx | exact Hx1].
  - destruct h.
    + pose proof (e_onseg_relation s1 n cx x y Hembed1 Hp1) as [_ Hx1].
      pose proof (e_onseg_relation s2 s cx x y Hembed2 Hp2) as [Hx2 _].
      apply on_segment_term_from_x; [exact Hp1 |]. simpl.
      apply Rle_antisym; [exact Hx1 | now rewrite Hjoinx].
    + pose proof (w_onseg_relation s1 n cx x y Hembed1 Hp1) as [Hx1 _].
      pose proof (w_onseg_relation s2 s cx x y Hembed2 Hp2) as [_ Hx2].
      apply on_segment_term_from_x; [exact Hp1 |]. simpl.
      apply Rle_antisym; [now rewrite Hjoinx | exact Hx1].
  - destruct h.
    + pose proof (e_onseg_relation s1 s cc x y Hembed1 Hp1) as [_ Hx1].
      pose proof (e_onseg_relation s2 n cc x y Hembed2 Hp2) as [Hx2 _].
      apply on_segment_term_from_x; [exact Hp1 |]. simpl.
      apply Rle_antisym; [exact Hx1 | now rewrite Hjoinx].
    + pose proof (w_onseg_relation s1 s cc x y Hembed1 Hp1) as [Hx1 _].
      pose proof (w_onseg_relation s2 n cc x y Hembed2 Hp2) as [_ Hx2].
      apply on_segment_term_from_x; [exact Hp1 |]. simpl.
      apply Rle_antisym; [now rewrite Hjoinx | exact Hx1].
  - pose proof (n_onseg_relation s1 h cc x y Hembed1 Hp1) as [_ Hy1].
    pose proof (n_onseg_relation s2 (i_h h) cx x y Hembed2 Hp2) as [Hy2 _].
    apply on_segment_term_from_y; [exact Hp1 |]. simpl.
    apply Rle_antisym; [exact Hy1 | now rewrite Hjoiny].
  - pose proof (s_onseg_relation s1 h cx x y Hembed1 Hp1) as [Hy1 _].
    pose proof (s_onseg_relation s2 (i_h h) cc x y Hembed2 Hp2) as [_ Hy2].
    apply on_segment_term_from_y; [exact Hp1 |]. simpl.
    apply Rle_antisym; [now rewrite Hjoiny | exact Hy1].
Qed.

Lemma embed_scurve_nth_embed : forall sc ls,
  embed_scurve sc ls ->
  forall i s, nth_error ls i = Some s ->
  exists ps, nth_error (proj1_sig sc) i = Some ps /\ embed ps s.
Proof.
  intros sc ls Hembed.
  induction Hembed as
    [| ps seg0 Hps | ps lp A s1 s2 rest Hps Htail IH Hjoin];
    intros i seg Hnth.
  - destruct i; discriminate.
  - destruct i as [|i]; simpl in Hnth.
    + injection Hnth as <-. exists ps. split; [reflexivity | exact Hps].
    + destruct i; discriminate.
  - destruct i as [|i]; simpl in Hnth.
    + injection Hnth as <-. exists ps. split; [reflexivity | exact Hps].
    + destruct (IH i seg Hnth) as [q [Hq Hqs]].
      exists q. split; [exact Hq | exact Hqs].
Qed.

Lemma is_scurve_adjacent_dc : forall ps i ps1 ps2,
  is_scurve ps ->
  nth_error ps i = Some ps1 ->
  nth_error ps (S i) = Some ps2 ->
  dc ps1 ps2.
Proof.
  intros ps i ps1 ps2 Hcurve. revert i ps1 ps2.
  induction Hcurve as [|p ps Hcurve IH Hhead]; intros i ps1 ps2 H1 H2.
  - destruct i; discriminate.
  - destruct i as [|i].
    + simpl in H1, H2. injection H1 as <-.
      destruct ps as [|q qs]; [discriminate|].
      simpl in H2. injection H2 as <-.
      inversion Hhead; subst. assumption.
    + simpl in H1, H2. eapply IH; eauto.
Qed.

Lemma embed_scurve_adjacent_data : forall sc ls i s1 s2,
  embed_scurve sc ls ->
  nth_error ls i = Some s1 ->
  nth_error ls (S i) = Some s2 ->
  exists ps1 ps2,
    embed ps1 s1 /\ embed ps2 s2 /\ dc ps1 ps2 /\ term s1 = init s2.
Proof.
  intros sc ls i s1 s2 Hembed H1 H2.
  destruct (embed_scurve_nth_embed sc ls Hembed i s1 H1)
    as [ps1 [Hp1 Hembed1]].
  destruct (embed_scurve_nth_embed sc ls Hembed (S i) s2 H2)
    as [ps2 [Hp2 Hembed2]].
  exists ps1, ps2. repeat split; try assumption.
  - eapply is_scurve_adjacent_dc; eauto. exact (proj2_sig sc).
  - eapply embed_scurve_connected; eauto.
Qed.

Lemma nonadjacent_sides_prefix : forall a l r s,
  In s (nonadjacent_sides l r) ->
  In s (nonadjacent_sides (a :: l) r).
Proof.
  intros a l r s. unfold nonadjacent_sides.
  destruct l as [|b l]; [simpl; tauto |].
  intros H. rewrite in_app_iff in H. rewrite in_app_iff.
  destruct H as [H | H].
  - left. simpl. now right.
  - now right.
Qed.

(* 添字が二つ以上離れた要素は、中心要素の非隣接部分に現れる。 *)
Lemma nth_error_far_in_nonadjacent_sides : forall ls i j s t,
  nth_error ls i = Some s ->
  nth_error ls j = Some t ->
  (S i < j \/ S j < i)%nat ->
  exists l r,
    ls = l ++ [s] ++ r /\ In t (nonadjacent_sides l r).
Proof.
  induction ls as [|a ls IH]; intros i j s t Hi Hj Hfar.
  - destruct i; discriminate.
  - destruct i as [|i], j as [|j].
    + lia.
    + simpl in Hi. injection Hi as <-.
      destruct j as [|j]; [lia|].
      simpl in Hj. destruct ls as [|b ls]; [discriminate|].
      simpl in Hj. exists [], (b :: ls). split; [reflexivity|].
      simpl. now apply nth_error_In in Hj.
    + simpl in Hj. injection Hj as <-.
      destruct i as [|i]; [lia|].
      simpl in Hi.
      destruct (@nth_error_split Segment ls (S i) s Hi)
        as [l [r [Hls Hlen]]].
      destruct l as [|b l]; [discriminate|].
      exists (a :: b :: l), r. split.
      * simpl. now rewrite Hls.
      * unfold nonadjacent_sides. rewrite in_app_iff. left. simpl. tauto.
    + simpl in Hi, Hj.
      destruct (IH i j s t Hi Hj ltac:(lia)) as [l [r [Hls Hin]]].
      exists (a :: l), r. split.
      * simpl. now rewrite Hls.
      * now apply nonadjacent_sides_prefix.
Qed.

(* 後のセグメントの始点以外の点は、それ以前のセグメント上に戻らない。 *)
Lemma later_body_point_not_on_earlier_segment :
  forall sc ls earlier later s_earlier s_later u,
    embed_scurve sc ls ->
    sparse_embedding ls ->
    nth_error ls earlier = Some s_earlier ->
    nth_error ls later = Some s_later ->
    (earlier < later)%nat ->
    0 < u <= 1 ->
    onSegment s_earlier (point s_later u) ->
    False.
Proof.
  intros sc ls earlier later s_earlier s_later u
    Hembed Hsparse Hearlier Hlater Hlt Hu HonEarlier.
  assert (HonLater : onSegment s_later (point s_later u)).
  { exists u. split; [lra | reflexivity]. }
  destruct (Nat.eq_dec later (S earlier)) as [Hadj | Hfar].
  - subst later.
    destruct (embed_scurve_adjacent_data
                sc ls earlier s_earlier s_later
                Hembed Hearlier Hlater)
      as [ps1 [ps2 [Hembed1 [Hembed2 [Hdc Hjoin]]]]].
    pose proof (adjacent_not_intersect_except_junction
                  ps1 ps2 s_earlier s_later (point s_later u)
                  Hdc Hembed1 Hembed2 Hjoin HonEarlier HonLater) as Hp.
    assert (Hzero : u = 0).
    { apply (point_injective s_later u 0).
      change (point s_later u = init s_later).
      now rewrite Hp. }
    lra.
  - assert (Hfar' : (S earlier < later)%nat) by lia.
    destruct (nth_error_far_in_nonadjacent_sides
                ls later earlier s_later s_earlier
                Hlater Hearlier ltac:(right; exact Hfar'))
      as [l [r [Hsplit Hin]]].
    destruct (Hsparse l s_later r Hsplit) as [_ Hrect].
    pose proof (Hrect s_earlier (point s_later u) Hin
                  (segment_in_rect_or_endpoints
                     s_earlier (point s_later u) HonEarlier)) as Havoid.
    apply Havoid. change (in_segment_rect_or_endpoints s_later (point s_later u)).
    exact (segment_in_rect_or_endpoints s_later (point s_later u) HonLater).
Qed.

Lemma sparse_body_collision_impossible : forall ls tb to sb so,
  ls <> [] ->
  (exists ds, embed_listDir ds ls) ->
  sparse_embedding ls ->
  nth_error ls (extend_index ls tb) = Some sb ->
  nth_error ls (extend_index ls to) = Some so ->
  extend_index ls tb <> extend_index ls to ->
  0 < extend_param ls tb <= 1 ->
  extend ls tb = point sb (extend_param ls tb) ->
  extend ls to = point so (extend_param ls to) ->
  extend ls tb = extend ls to ->
  False.
(* 非隣接なら sparse の長方形分離、隣接なら PrimitiveSegment
   埋め込みの方向条件から、異なる piece の衝突を除く。 *)
Proof.
  intros ls tb to sb so Hne [ds [sc [_ Hembed]]] Hsparse
    Hnthb Hntho Hindices Hbodyb Hreprb Hrepro Hcollision.
  set (ib := extend_index ls tb) in *.
  set (io := extend_index ls to) in *.
  set (ub := extend_param ls tb) in *.
  set (uo := extend_param ls to) in *.
  assert (Hpoints : point sb ub = point so uo).
  { rewrite <- Hreprb, <- Hrepro. exact Hcollision. }
  assert (Honb : onSegment sb (point sb ub)).
  { exists ub. split; [split; lra | reflexivity]. }
  assert (Hboxb : in_rect_or_endpoints_at [sb] (point sb ub)).
  { change (in_segment_rect_or_endpoints sb (point sb ub)).
    now apply segment_in_rect_or_endpoints. }
  destruct (extend_param_region ls to Hne)
    as [Hbodyo | [[Hio0 Huo] | [Hiolast Huo]]].
  - assert (Hono : onSegment so (point so uo)).
    { exists uo. split.
      - split; [now apply Rlt_le | exact (proj2 Hbodyo)].
      - reflexivity. }
    destruct (Nat.lt_trichotomy ib io) as [Hlt | [Heq | Hgt]].
    + eapply (later_body_point_not_on_earlier_segment
                sc ls ib io sb so uo Hembed Hsparse
                Hnthb Hntho Hlt Hbodyo).
      rewrite <- Hpoints. exact Honb.
    + now apply Hindices.
    + eapply (later_body_point_not_on_earlier_segment
                sc ls io ib so sb ub Hembed Hsparse
                Hntho Hnthb Hgt Hbodyb).
      rewrite Hpoints. exact Hono.
  - change (io = 0%nat) in Hio0.
    change (uo <= 0) in Huo.
    destruct (Rlt_dec uo 0) as [Huostrict | Huozero].
    + destruct (@nth_error_split Segment ls ib sb Hnthb)
        as [l [r [Hsplit _]]].
      destruct (Hsparse l sb r Hsplit) as [Hextend _].
      assert (Hwhole : l ++ [sb] ++ r = ls).
      { change (l ++ sb :: r = ls). now symmetry. }
      apply (Hextend (point sb ub)).
      * left. rewrite Hwhole. unfold onHead_extend_strict.
        assert (Hso : so = hd_segment ls).
        { rewrite Hio0 in Hntho. unfold hd_segment. symmetry.
          eapply nth_error_hd; exact Hntho. }
        exists uo. split; [exact Huostrict |].
        rewrite <- Hso, <- Hpoints. reflexivity.
      * exact Hboxb.
    + assert (Huo0 : uo = 0) by lra.
      assert (Hlt : (io < ib)%nat) by lia.
      eapply (later_body_point_not_on_earlier_segment
                sc ls io ib so sb ub Hembed Hsparse
                Hntho Hnthb Hlt Hbodyb).
      rewrite Hpoints, Huo0. apply onInit.
  - change (S io = length ls) in Hiolast.
    change (1 < uo) in Huo.
    destruct (@nth_error_split Segment ls ib sb Hnthb)
      as [l [r [Hsplit _]]].
    destruct (Hsparse l sb r Hsplit) as [Hextend _].
    assert (Hwhole : l ++ [sb] ++ r = ls).
    { change (l ++ sb :: r = ls). now symmetry. }
    apply (Hextend (point sb ub)).
    + right. rewrite Hwhole. unfold onLast_extend_strict.
      assert (Hso : so = last_segment ls).
      { unfold last_segment.
        assert (K : io = (length ls - 1)%nat) by lia.
        rewrite K in Hntho.
        pose proof (@nth_error_last Segment ls default_segment Hne) as Hlast.
        rewrite Hntho in Hlast. now injection Hlast. }
      exists uo. split; [exact Huo |].
      rewrite <- Hso, <- Hpoints. reflexivity.
    + exact Hboxb.
Qed.

Lemma sparse_extensions_open :
  forall ds ls,
    ls <> [] ->
    embed_listDir ds ls ->
    sparse_embedding ls ->
    extensions_disjoint ls ->
    ~ close ls.
Proof.
  intros ds ls Hne Hembed Hsparse Hdisjoint [t1 [t2 [Hneq Heq]]].
  destruct (extend_repr ls t1 Hne) as [s1 [Hnth1 Hrepr1]].
  destruct (extend_repr ls t2 Hne) as [s2 [Hnth2 Hrepr2]].
  assert (Hpoint : point s1 (extend_param ls t1) =
                   point s2 (extend_param ls t2)).
  { now rewrite <- Hrepr1, <- Hrepr2. }
  destruct (extend_param_region ls t1 Hne) as [Hbody1 | [Hhead1 | Hlast1]];
  destruct (extend_param_region ls t2 Hne) as [Hbody2 | [Hhead2 | Hlast2]].
  - destruct (Nat.eq_dec (extend_index ls t1) (extend_index ls t2)) as [Hi|Hi].
    + apply Hneq. exact (same_extend_piece_no_collision ls t1 t2 s1 s2 Hne Hnth1 Hnth2 Hi Hpoint).
    + eapply (sparse_body_collision_impossible ls t1 t2 s1 s2
                Hne (ex_intro _ ds Hembed) Hsparse Hnth1 Hnth2 Hi Hbody1 Hrepr1 Hrepr2 Heq).
  - destruct (Nat.eq_dec (extend_index ls t1) (extend_index ls t2)) as [Hi|Hi].
    + apply Hneq. exact (same_extend_piece_no_collision ls t1 t2 s1 s2 Hne Hnth1 Hnth2 Hi Hpoint).
    + eapply (sparse_body_collision_impossible ls t1 t2 s1 s2
                Hne (ex_intro _ ds Hembed) Hsparse Hnth1 Hnth2 Hi Hbody1 Hrepr1 Hrepr2 Heq).
  - destruct (Nat.eq_dec (extend_index ls t1) (extend_index ls t2)) as [Hi|Hi].
    + apply Hneq. exact (same_extend_piece_no_collision ls t1 t2 s1 s2 Hne Hnth1 Hnth2 Hi Hpoint).
    + eapply (sparse_body_collision_impossible ls t1 t2 s1 s2
                Hne (ex_intro _ ds Hembed) Hsparse Hnth1 Hnth2 Hi Hbody1 Hrepr1 Hrepr2 Heq).
  - destruct (Nat.eq_dec (extend_index ls t1) (extend_index ls t2)) as [Hi|Hi].
    + apply Hneq. exact (same_extend_piece_no_collision ls t1 t2 s1 s2 Hne Hnth1 Hnth2 Hi Hpoint).
    + eapply (sparse_body_collision_impossible ls t2 t1 s2 s1
                Hne (ex_intro _ ds Hembed) Hsparse Hnth2 Hnth1 ltac:(congruence) Hbody2
                Hrepr2 Hrepr1 ltac:(congruence)).
  - apply Hneq. eapply same_extend_piece_no_collision; eauto; lia.
  - apply (Hdisjoint (extend ls t1)).
    + destruct Hhead1 as [Hi1 Hp1].
      exact (extend_head_from_repr ls t1 s1 Hne Hnth1 Hrepr1 Hi1 Hp1).
    + rewrite Heq. destruct Hlast2 as [Hi2 Hp2].
      exact (extend_last_from_repr ls t2 s2 Hne Hnth2 Hrepr2 Hi2 Hp2).
  - destruct (Nat.eq_dec (extend_index ls t1) (extend_index ls t2)) as [Hi|Hi].
    + apply Hneq. exact (same_extend_piece_no_collision ls t1 t2 s1 s2 Hne Hnth1 Hnth2 Hi Hpoint).
    + eapply (sparse_body_collision_impossible ls t2 t1 s2 s1
                Hne (ex_intro _ ds Hembed) Hsparse Hnth2 Hnth1 ltac:(congruence) Hbody2
                Hrepr2 Hrepr1 ltac:(congruence)).
  - apply (Hdisjoint (extend ls t2)).
    + destruct Hhead2 as [Hi2 Hp2].
      exact (extend_head_from_repr ls t2 s2 Hne Hnth2 Hrepr2 Hi2 Hp2).
    + rewrite <- Heq. destruct Hlast1 as [Hi1 Hp1].
      exact (extend_last_from_repr ls t1 s1 Hne Hnth1 Hrepr1 Hi1 Hp1).
  - apply Hneq. eapply same_extend_piece_no_collision; eauto; lia.
Qed.

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

Lemma rot_sparse_embedding :
  forall g ls,
    sparse_embedding ls ->
    sparse_embedding (rot_segs g ls).
Admitted.

Lemma rot_extensions_disjoint :
  forall g ls,
    extensions_disjoint ls ->
    extensions_disjoint (rot_segs g ls).
Admitted.


(* ================================================================= *)
(*  3.  sub と移動量                                                 *)
(* ================================================================= *)

Parameter bbox_of : list Segment -> Rect.
Axiom bbox_of_bounds :
  forall sub p, onSegmentlist sub p ->
    ry0 (bbox_of sub) <= snd p <= ry1 (bbox_of sub).

Definition well_split (l sub r : list Segment) : Prop :=
  sub <> [] /\ x_monotone_segs sub /\ ~ close (l ++ sub ++ r).

Definition h_large (h : R) (sub : list Segment) : Prop :=
  0 < h /\ rect_height (bbox_of sub) < h.

Lemma choose_h : forall sub, exists h, h_large h sub.
Proof.
  intros sub. exists (Rmax 1 (rect_height (bbox_of sub) + 1)).
  unfold h_large. split.
  - eapply Rlt_le_trans; [apply Rlt_0_1 | apply Rmax_l].
  - eapply Rlt_le_trans; [| apply Rmax_r]. lra.
Qed.


(* ================================================================= *)
(*  4.  端点の分類と上下移動                                         *)
(* ================================================================= *)

Inductive Region : Type := RegFix | RegUp | RegDown.

Inductive region_above : Region -> Region -> Prop :=
  | RegUp_above_Fix : region_above RegUp RegFix
  | RegUp_above_Down : region_above RegUp RegDown
  | RegFix_above_Down : region_above RegFix RegDown.

Definition region_at_or_above (g1 g2 : Region) : Prop :=
  g1 = g2 \/ region_above g1 g2.

Lemma region_above_not_reverse :
  forall g1 g2,
    region_above g1 g2 -> ~ region_at_or_above g2 g1.
Proof.
  intros g1 g2 H. destruct H; intros [Heq | Hrev];
    try discriminate; inversion Hrev.
Qed.

Lemma Region_eq_dec : forall g1 g2 : Region, {g1 = g2} + {g1 <> g2}.
Proof. decide equality. Qed.

Definition endpoint_of_seg (s : Segment) (p : Point) : Prop :=
  p = init s \/ p = term s.

Definition endpoint_of (ls : list Segment) (p : Point) : Prop :=
  exists s, In s ls /\ endpoint_of_seg s p.

Lemma endpoint_of_onSegmentlist : forall ls p,
  endpoint_of ls p -> onSegmentlist ls p.
Proof.
  intros ls p [s [Hs Hend]]. exists s. split; [exact Hs |].
  destruct Hend as [Hp | Hp].
  - subst p. apply onInit.
  - subst p. apply onTerm.
Qed.

(* 分類は曲線全体の配置を見て選ぶ。sub 上の端点は固定し、全体の先頭と
   末尾では延長線の傾きを平行移動で保てる配置を要求する。 *)
Parameter classify :
  list Segment -> list Segment -> list Segment -> Point -> Region.

Definition above_head_extension (ls : list Segment) (p : Point) : Prop :=
  exists q,
    onHead_extend ls q /\ fst q = fst p /\ snd q < snd p.

Definition below_head_extension (ls : list Segment) (p : Point) : Prop :=
  exists q,
    onHead_extend ls q /\ fst q = fst p /\ snd p < snd q.

Definition above_last_extension (ls : list Segment) (p : Point) : Prop :=
  exists q,
    onLast_extend ls q /\ fst q = fst p /\ snd q < snd p.

Definition below_last_extension (ls : list Segment) (p : Point) : Prop :=
  exists q,
    onLast_extend ls q /\ fst q = fst p /\ snd p < snd q.

Definition in_sub_x_range (sub : list Segment) (p : Point) : Prop :=
  rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub).

Definition above_sub_at_x (sub : list Segment) (p : Point) : Prop :=
  exists q,
    onSegmentlist sub q
    /\ fst p = fst q
    /\ snd q < snd p.

Definition below_sub_at_x (sub : list Segment) (p : Point) : Prop :=
  exists q,
    onSegmentlist sub q
    /\ fst p = fst q
    /\ snd p < snd q.

Record ClassificationSpec (l sub r : list Segment) : Prop := {
  classified_sub_fixed :
    forall p, onSegmentlist sub p -> classify l sub r p = RegFix;

  classified_segment_endpoints_monotone :
    forall s,
      In s (l ++ sub ++ r) ->
      (snd (init s) < snd (term s) ->
        region_at_or_above (classify l sub r (term s)) (classify l sub r (init s)))
      /\
      (snd (term s) < snd (init s) ->
        region_at_or_above (classify l sub r (init s)) (classify l sub r (term s)));

  classified_same_x_monotone :
    forall p q,
      fst p = fst q ->
      snd p < snd q ->
      region_at_or_above (classify l sub r q) (classify l sub r p);

  (* 非隣接セグメントの端点間で、上下移動が元の上下順序を逆転させない。 *)
  classified_nonadjacent_endpoint_order :
    forall i j s t ps pt,
      nth_error (l ++ sub ++ r) i = Some s ->
      nth_error (l ++ sub ++ r) j = Some t ->
      (S i < j \/ S j < i)%nat ->
      endpoint_of_seg s ps ->
      endpoint_of_seg t pt ->
      snd ps <= snd pt ->
      region_at_or_above
        (classify l sub r pt) (classify l sub r ps);

  classified_above_fix_up :
    forall p q,
      fst p = fst q ->
      classify l sub r p = RegFix ->
      snd p < snd q ->
      classify l sub r q = RegUp;

  classified_below_fix_down :
    forall p q,
      fst p = fst q ->
      classify l sub r p = RegFix ->
      snd q < snd p ->
      classify l sub r q = RegDown;

  (* sub と同じ x にあるセグメント上の点の上下側を、両端点へ伝える。 *)
  classified_segment_at_sub_x :
    forall s p,
      In s (nonadjacent_sides l r) ->
      onSegment s p ->
      in_sub_x_range sub p ->
      (above_sub_at_x sub p ->
         classify l sub r (init s) = RegUp
         /\ classify l sub r (term s) = RegUp)
      /\
      (below_sub_at_x sub p ->
         classify l sub r (init s) = RegDown
         /\ classify l sub r (term s) = RegDown);

  (* strict 延長線が sub 長方形の開 x 範囲へ入る場合，
     その延長線を動かす基点は Fix ではない。 *)
  classified_head_extension_at_sub_x :
    forall p,
      onHead_extend_strict (l ++ sub ++ r) p ->
      rx0 (rect_of sub) < fst p < rx1 (rect_of sub) ->
      classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegUp
      \/ classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegDown;

  classified_last_extension_at_sub_x :
    forall p,
      onLast_extend_strict (l ++ sub ++ r) p ->
      rx0 (rect_of sub) < fst p < rx1 (rect_of sub) ->
      classify l sub r (term (last_segment (l ++ sub ++ r))) = RegUp
      \/ classify l sub r (term (last_segment (l ++ sub ++ r))) = RegDown;

  classified_head_same_region :
    l <> [] ->
    classify l sub r (init (hd_segment l)) =
      classify l sub r (term (hd_segment l))
    \/ (term (hd_segment l) = init (hd_segment sub) (* l = [s] (singleton) の場合 *)
        /\ fst (init (hd_segment sub)) < fst (init (hd_segment l)));

  classified_last_same_region :
    r <> [] ->
    classify l sub r (init (last_segment r)) =
      classify l sub r (term (last_segment r))
    \/ (init (last_segment r) = term (last_segment sub) (* r = [s] (singleton) の場合 *)
        /\ fst (term (last_segment r)) < fst (term (last_segment sub)));

  (* 全体の始点が RegUp なら，先頭延長線より上にある点も RegUp *)
  classified_above_head_up :
    classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegUp ->
    forall p,
      above_head_extension (l ++ sub ++ r) p ->
      classify l sub r p = RegUp;

  classified_below_head_down :
    classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegDown ->
    forall p,
      below_head_extension (l ++ sub ++ r) p ->
      classify l sub r p = RegDown;

  classified_above_last_up :
    classify l sub r (term (last_segment (l ++ sub ++ r))) = RegUp ->
    forall p,
      above_last_extension (l ++ sub ++ r) p ->
      classify l sub r p = RegUp;

  classified_below_last_down :
    classify l sub r (term (last_segment (l ++ sub ++ r))) = RegDown ->
    forall p,
      below_last_extension (l ++ sub ++ r) p ->
      classify l sub r p = RegDown
}.

Axiom classify_spec :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    ClassificationSpec l sub r.

(* 同じ x 上の分類単調性から、異なる領域の点の上下順序を逆に読む。 *)
Lemma classified_vertical_order :
  forall l sub r p q,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    fst p = fst q ->
    region_above (classify l sub r p) (classify l sub r q) ->
    snd q < snd p.
Proof.
  intros l sub r p q Hne Hconn Hmono Hsparse Hx Habove.
  destruct (total_order_T (snd q) (snd p)) as [[Hlt | Heq] | Hgt].
  - exact Hlt.
  - exfalso. apply (region_above_not_reverse _ _ Habove).
    left. f_equal. destruct p as [xp yp], q as [xq yq].
    simpl in Hx, Heq |- *. f_equal; lra.
  - exfalso. apply (region_above_not_reverse _ _ Habove).
    eapply classified_same_x_monotone.
    + exact (classify_spec l sub r Hne Hconn Hmono Hsparse).
    + exact Hx.
    + exact Hgt.
Qed.

(* Fix と同じ x の Up/Down は、Fix より厳密に上/下にある。 *)
Lemma classified_up_above_fix :
  forall l sub r p q,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    fst p = fst q ->
    classify l sub r q = RegFix ->
    classify l sub r p = RegUp ->
    snd q < snd p.
Proof.
  intros l sub r p q Hne Hconn Hmono Hsparse Hx Hfix Hup.
  destruct (total_order_T (snd q) (snd p)) as [[Hlt | Heq] | Hgt].
  - exact Hlt.
  - assert (Hpq : p = q).
    { destruct p as [xp yp], q as [xq yq].
      simpl in Hx, Heq |- *. f_equal; lra. }
    subst p. congruence.
  - pose proof (classified_below_fix_down
                  l sub r
                  (classify_spec l sub r Hne Hconn Hmono Hsparse)
                  q p ltac:(symmetry; exact Hx) Hfix Hgt) as Hdown.
    congruence.
Qed.

Lemma classified_down_below_fix :
  forall l sub r p q,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    fst p = fst q ->
    classify l sub r q = RegFix ->
    classify l sub r p = RegDown ->
    snd p < snd q.
Proof.
  intros l sub r p q Hne Hconn Hmono Hsparse Hx Hfix Hdown.
  destruct (total_order_T (snd p) (snd q)) as [[Hlt | Heq] | Hgt].
  - exact Hlt.
  - assert (Hpq : p = q).
    { destruct p as [xp yp], q as [xq yq].
      simpl in Hx, Heq |- *. f_equal; lra. }
    subst p. congruence.
  - pose proof (classified_above_fix_up
                  l sub r
                  (classify_spec l sub r Hne Hconn Hmono Hsparse)
                  q p ltac:(symmetry; exact Hx) Hfix Hgt) as Hup.
    congruence.
Qed.

Lemma connected_x_monotone_endpoints :
  forall sub,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    fst (init (hd_segment sub)) < fst (term (last_segment sub)).
Proof.
  intros sub Hne. destruct sub as [|a tail]; [contradiction|].
  clear Hne.
  revert a. induction tail as [|b tail IH]; intros a Hconn Hmono.
  - apply Hmono. now left.
  - assert (Hab : term a = init b).
    { apply (Hconn 0%nat a b); reflexivity. }
    assert (HconnTail : connected (b :: tail)).
    { intros i s1 s2 H1 H2.
      apply (Hconn (S i) s1 s2); simpl; assumption. }
    assert (HmonoTail : x_monotone_segs (b :: tail)).
    { intros t Ht. apply Hmono. now right. }
    pose proof (IH b HconnTail HmonoTail) as Htail.
    pose proof (Hmono a ltac:(now left)) as Ha.
    change (fst (init a) < fst (term (last_segment (b :: tail)))).
    change (fst (init b) < fst (term (last_segment (b :: tail)))) in Htail.
    unfold x_monotone_seg, init_x, term_x in Ha.
    rewrite Hab in Ha. lra.
Qed.

(* x 単調な連結列では、全体長方形の左右端は列の始終点である。 *)
Lemma x_monotone_rect_x_bounds :
  forall sub,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    rx0 (rect_of sub) = fst (init (hd_segment sub))
    /\ rx1 (rect_of sub) = fst (term (last_segment sub)).
Proof.
  intros sub Hne Hconn Hmono.
  pose proof (connected_x_monotone_endpoints sub Hne Hconn Hmono) as Hends.
  unfold rect_of; simpl.
  rewrite Rmin_left by lra.
  rewrite Rmax_right by lra.
  split; reflexivity.
Qed.

(* セグメントの端点 x 区間内の各 x 座標は、セグメント上で実現される。 *)
Lemma segment_has_point_at_x :
  forall s x,
    rx0 (rect_of [s]) <= x <= rx1 (rect_of [s]) ->
    exists p, onSegment s p /\ fst p = x.
Proof.
  intros s x Hx.
  destruct (total_order_T (fst (init s)) (fst (term s)))
    as [[Hix | Heq] | Htx].
  - change (Rmin (fst (init s)) (fst (term s)) <= x <=
            Rmax (fst (init s)) (fst (term s))) in Hx.
    rewrite Rmin_left in Hx by lra.
    rewrite Rmax_right in Hx by lra.
    destruct (Rle_dec (snd (init s)) (snd (term s))) as [Hy | Hy].
    + destruct (exist_between_x_pos s
                  (fst (init s)) (fst (term s))
                  (snd (init s)) (snd (term s)) x
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  Hy (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
    + destruct (exist_between_x_neg s
                  (fst (init s)) (fst (term s))
                  (snd (init s)) (snd (term s)) x
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  ltac:(lra) (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
  - exfalso. apply (neq_init_term_x s).
    unfold init_x, term_x. exact Heq.
  - change (Rmin (fst (init s)) (fst (term s)) <= x <=
            Rmax (fst (init s)) (fst (term s))) in Hx.
    rewrite Rmin_right in Hx by lra.
    rewrite Rmax_left in Hx by lra.
    destruct (Rle_dec (snd (term s)) (snd (init s))) as [Hy | Hy].
    + destruct (exist_between_x_pos s
                  (fst (term s)) (fst (init s))
                  (snd (term s)) (snd (init s)) x
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  Hy (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
    + destruct (exist_between_x_neg s
                  (fst (term s)) (fst (init s))
                  (snd (term s)) (snd (init s)) x
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  ltac:(lra) (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
Qed.

(* 連結な x 単調 sub は、始終点間の各 x 座標を通る。 *)
Lemma x_monotone_sub_has_point :
  forall sub x,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    rx0 (rect_of sub) <= x <= rx1 (rect_of sub) ->
    exists q, onSegmentlist sub q /\ fst q = x.
Proof.
  intros sub x Hne. destruct sub as [|a tail]; [contradiction|].
  clear Hne. revert a x.
  induction tail as [|b tail IH]; intros a x Hconn Hmono Hx.
  - destruct (segment_has_point_at_x a x Hx) as [q [Hon Hqx]].
    exists q. split; [exists a; split; [now left | exact Hon] | exact Hqx].
  - assert (Hab : term a = init b).
    { apply (Hconn 0%nat a b); reflexivity. }
    assert (HconnTail : connected (b :: tail)).
    { intros i s1 s2 H1 H2.
      apply (Hconn (S i) s1 s2); simpl; assumption. }
    assert (HmonoTail : x_monotone_segs (b :: tail)).
    { intros s Hs. apply Hmono. now right. }
    pose proof (x_monotone_rect_x_bounds
                  (a :: b :: tail) ltac:(discriminate) Hconn Hmono)
      as [Hleft Hright].
    change (rx0 (rect_of (a :: b :: tail)) = fst (init a)) in Hleft.
    assert (Hlast :
      last_segment (a :: b :: tail) = last_segment (b :: tail)).
    { change (last_segment ([a] ++ b :: tail) = last_segment (b :: tail)).
      apply last_app_nonnil. discriminate. }
    rewrite Hleft, Hright in Hx.
    destruct (Rle_dec x (fst (term a))) as [Hxa | Hax].
    + assert (Hsingle :
          rx0 (rect_of [a]) <= x <= rx1 (rect_of [a])).
      { pose proof (Hmono a ltac:(now left)) as Ha.
        unfold x_monotone_seg, init_x, term_x in Ha.
        change (Rmin (fst (init a)) (fst (term a)) <= x <=
                Rmax (fst (init a)) (fst (term a))).
        rewrite Rmin_left by lra. rewrite Rmax_right by lra.
        lra. }
      destruct (segment_has_point_at_x a x Hsingle) as [q [Hon Hqx]].
      exists q. split.
      * exists a. split; [now left | exact Hon].
      * exact Hqx.
    + assert (Htailx :
          rx0 (rect_of (b :: tail)) <= x <=
          rx1 (rect_of (b :: tail))).
      { pose proof (x_monotone_rect_x_bounds
                      (b :: tail) ltac:(discriminate)
                      HconnTail HmonoTail) as [HtailLeft HtailRight].
        change (rx0 (rect_of (b :: tail)) = fst (init b)) in HtailLeft.
        rewrite HtailLeft, HtailRight.
        rewrite Hlast in Hx.
        rewrite Hab in Hax. lra. }
      destruct (IH b x HconnTail HmonoTail Htailx)
        as [q [[s [Hs Hon]] Hqx]].
      exists q. split.
      * exists s. split; [now right | exact Hon].
      * exact Hqx.
Qed.

Lemma classified_up_above_bbox_floor :
  forall l sub r p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub) ->
    classify l sub r p = RegUp ->
    ry0 (bbox_of sub) < snd p.
Proof.
  intros l sub r p Hne Hconn Hmono Hsparse Hx Hup.
  destruct (x_monotone_sub_has_point sub (fst p) Hne Hconn Hmono Hx)
    as [q [Hqsub Hqx]].
  pose proof (classified_sub_fixed
                l sub r (classify_spec l sub r Hne Hconn Hmono Hsparse)
                q Hqsub) as Hfix.
  pose proof (classified_up_above_fix
                l sub r p q Hne Hconn Hmono Hsparse
                ltac:(symmetry; exact Hqx) Hfix Hup) as Hy.
  pose proof (bbox_of_bounds sub q Hqsub) as [Hlo _].
  lra.
Qed.

Lemma classified_down_below_bbox_ceiling :
  forall l sub r p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub) ->
    classify l sub r p = RegDown ->
    snd p < ry1 (bbox_of sub).
Proof.
  intros l sub r p Hne Hconn Hmono Hsparse Hx Hdown.
  destruct (x_monotone_sub_has_point sub (fst p) Hne Hconn Hmono Hx)
    as [q [Hqsub Hqx]].
  pose proof (classified_sub_fixed
                l sub r (classify_spec l sub r Hne Hconn Hmono Hsparse)
                q Hqsub) as Hfix.
  pose proof (classified_down_below_fix
                l sub r p q Hne Hconn Hmono Hsparse
                ltac:(symmetry; exact Hqx) Hfix Hdown) as Hy.
  pose proof (bbox_of_bounds sub q Hqsub) as [_ Hhi].
  lra.
Qed.

Definition shift (h : R) (g : Region) (p : Point) : Point :=
  match g with
  | RegFix  => p
  | RegUp   => (fst p, snd p + h)
  | RegDown => (fst p, snd p - h)
  end.

Definition region_translation (h : R) (g : Region) : Point :=
  match g with
  | RegFix => (0, 0)
  | RegUp => (0, h)
  | RegDown => (0, - h)
  end.

Lemma shift_as_translation :
  forall h g p, shift h g p = translate_pt (region_translation h g) p.
Proof.
  intros h g [x y]. destruct g; unfold shift, region_translation, translate_pt;
    simpl; f_equal; ring.
Qed.

Lemma shift_preserves_strict_vertical_order :
  forall h p q gp gq,
    0 < h ->
    snd p < snd q ->
    region_at_or_above gq gp ->
    snd (shift h gp p) < snd (shift h gq q).
Proof.
  intros h [xp yp] [xq yq] gp gq Hh Hy [Heq | Habove].
  - subst gq. destruct gp; simpl in Hy |- *; lra.
  - destruct Habove; simpl in Hy |- *; lra.
Qed.

Lemma shift_preserves_vertical_order :
  forall h p q gp gq,
    0 < h ->
    snd p <= snd q ->
    region_at_or_above gq gp ->
    snd (shift h gp p) <= snd (shift h gq q).
Proof.
  intros h [xp yp] [xq yq] gp gq Hh Hy [Heq | Habove].
  - subst gq. destruct gp; simpl in Hy |- *; lra.
  - destruct Habove; simpl in Hy |- *; lra.
Qed.

Definition operate_point
  (l sub r : list Segment) (h : R) (p : Point) : Point :=
  shift h (classify l sub r p) p.

Lemma shift_fst :
  forall h g p, fst (shift h g p) = fst p.
Proof. intros h g p. destruct g; reflexivity. Qed.

Lemma operate_point_fst :
  forall l sub r h p, fst (operate_point l sub r h p) = fst p.
Proof. intros. unfold operate_point. apply shift_fst. Qed.

(* 同じ x 上の分類単調性により、正の高さの上下移動は平面上で単射となる。 *)
Lemma operate_point_injective :
  forall l sub r h p q,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    0 < h ->
    operate_point l sub r h p = operate_point l sub r h q ->
    p = q.
Proof.
  intros l sub r h [xp yp] [xq yq]
    Hne Hconn Hmono Hsparse Hh Heq.
  destruct (classify l sub r (xp, yp)) eqn:Hrp;
  destruct (classify l sub r (xq, yq)) eqn:Hrq;
  unfold operate_point, shift in Heq; rewrite Hrp, Hrq in Heq;
  pose proof (f_equal fst Heq) as Hx;
  pose proof (f_equal snd Heq) as Hy; simpl in Hx, Hy.
  - f_equal; lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xq, yq) (xp, yp) Hne Hconn Hmono Hsparse
                  ltac:(symmetry; exact Hx)
                  ltac:(rewrite Hrq, Hrp; constructor)) as Horder.
    simpl in Horder. lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xp, yp) (xq, yq) Hne Hconn Hmono Hsparse
                  ltac:(exact Hx)
                  ltac:(rewrite Hrp, Hrq; constructor)) as Horder.
    simpl in Horder. lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xp, yp) (xq, yq) Hne Hconn Hmono Hsparse
                  ltac:(exact Hx)
                  ltac:(rewrite Hrp, Hrq; constructor)) as Horder.
    simpl in Horder. lra.
  - f_equal; lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xp, yp) (xq, yq) Hne Hconn Hmono Hsparse
                  ltac:(exact Hx)
                  ltac:(rewrite Hrp, Hrq; constructor)) as Horder.
    simpl in Horder. lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xq, yq) (xp, yp) Hne Hconn Hmono Hsparse
                  ltac:(symmetry; exact Hx)
                  ltac:(rewrite Hrq, Hrp; constructor)) as Horder.
    simpl in Horder. lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xq, yq) (xp, yp) Hne Hconn Hmono Hsparse
                  ltac:(symmetry; exact Hx)
                  ltac:(rewrite Hrq, Hrp; constructor)) as Horder.
    simpl in Horder. lra.
  - f_equal; lra.
Qed.

Lemma operate_point_RegFix :
  forall l sub r h p,
    classify l sub r p = RegFix ->
    operate_point l sub r h p = p.
Proof.
  intros l sub r h p H. unfold operate_point. now rewrite H.
Qed.

Lemma classify_sub_endpoint :
  forall l sub r p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    endpoint_of sub p ->
    classify l sub r p = RegFix.
Proof.
  intros l sub r p Hne Hconn Hmono Hsparse Hend.
  exact (classified_sub_fixed
           l sub r
           (classify_spec l sub r Hne Hconn Hmono Hsparse)
           p (endpoint_of_onSegmentlist sub p Hend)).
Qed.

Lemma operate_sub_endpoint :
  forall l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    endpoint_of sub p ->
    operate_point l sub r h p = p.
Proof.
  intros l sub r h p Hne Hconn Hmono Hsparse Hend.
  apply operate_point_RegFix.
  now apply classify_sub_endpoint.
Qed.


(* ================================================================= *)
(*  5.  端点移動後の再接続                                           *)
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
      | right _ => make_seg
          (operate_point l sub r h (init s))
          (operate_point l sub r h (term s))
          (orn_seg s) H
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

Lemma reconnect_one_init :
  forall l sub r h s,
    reconnectable_after l sub r h s ->
    init (reconnect_one l sub r h s) = operate_point l sub r h (init s).
Proof.
  intros l sub r h s Hrec. unfold reconnect_one.
  destruct (excluded_middle_informative
              (reconnectable_after l sub r h s)) as [H | H].
  - destruct (excluded_middle_informative
                (reconnect_slope_after l sub r h s)) as [Hs | Hs].
    + exact (proj1 (make_seg_slope_spec _ _ _ _ _ Hs)).
    + now apply make_seg_init.
  - contradiction.
Qed.

Lemma reconnect_one_term :
  forall l sub r h s,
    reconnectable_after l sub r h s ->
    term (reconnect_one l sub r h s) = operate_point l sub r h (term s).
Proof.
  intros l sub r h s Hrec. unfold reconnect_one.
  destruct (excluded_middle_informative
              (reconnectable_after l sub r h s)) as [H | H].
  - destruct (excluded_middle_informative
                (reconnect_slope_after l sub r h s)) as [Hs | Hs].
    + exact (proj1 (proj2 (make_seg_slope_spec _ _ _ _ _ Hs))).
    + now apply make_seg_term.
  - contradiction.
Qed.

Lemma reconnect_one_orn :
  forall l sub r h s,
    reconnectable_after l sub r h s ->
    orn_seg (reconnect_one l sub r h s) = orn_seg s.
Proof.
  intros l sub r h s Hrec. unfold reconnect_one.
  destruct (excluded_middle_informative
              (reconnectable_after l sub r h s)) as [H | H].
  - destruct (excluded_middle_informative
                (reconnect_slope_after l sub r h s)) as [Hs | Hs].
    + exact (proj1 (proj2 (proj2
        (make_seg_slope_spec _ _ _ _ _ Hs)))).
    + now apply make_seg_orn.
  - contradiction.
Qed.

Lemma reconnect_one_slope_init :
  forall l sub r h s,
    reconnect_slope_after l sub r h s ->
    slope_init (reconnect_one l sub r h s) = slope_init s.
Proof.
  intros l sub r h s Hslope. unfold reconnect_one.
  destruct (excluded_middle_informative
              (reconnectable_after l sub r h s)) as [Hrec | Hrec].
  - destruct (excluded_middle_informative
                (reconnect_slope_after l sub r h s)) as [Hs | Hs].
    + exact (proj1 (proj2 (proj2 (proj2
        (make_seg_slope_spec _ _ _ _ _ Hs))))).
    + contradiction.
  - exfalso. apply Hrec. unfold reconnectable_after.
    now apply reconnect_slope_reconnectable with
      (slope_p := slope_init s) (slope_q := slope_term s).
Qed.

Lemma reconnect_one_slope_term :
  forall l sub r h s,
    reconnect_slope_after l sub r h s ->
    slope_term (reconnect_one l sub r h s) = slope_term s.
Proof.
  intros l sub r h s Hslope. unfold reconnect_one.
  destruct (excluded_middle_informative
              (reconnectable_after l sub r h s)) as [Hrec | Hrec].
  - destruct (excluded_middle_informative
                (reconnect_slope_after l sub r h s)) as [Hs | Hs].
    + exact (proj2 (proj2 (proj2 (proj2
        (make_seg_slope_spec _ _ _ _ _ Hs))))).
    + contradiction.
  - exfalso. apply Hrec. unfold reconnectable_after.
    now apply reconnect_slope_reconnectable with
      (slope_p := slope_init s) (slope_q := slope_term s).
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

(* sub 側の端点だけを固定する先頭の特例でも、両端傾きを指定できる。 *)
(* 考慮すべきは，例えば右上に向かって sub = [+-+], l = [(+ の埋め込み)] など．
    l の始点は上下せざるを得ないが，うまくセグメントを取ることでそこでの傾きは保存できる *)
Lemma reconnect_head_fixed_endpoint_slope :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    l <> [] ->
    term (hd_segment l) = init (hd_segment sub) ->
    fst (init (hd_segment sub)) < fst (init (hd_segment l)) ->
    reconnect_slope_after l sub r h (hd_segment l).
Admitted.

(* sub 側の端点だけを固定する末尾の特例。 *)
Lemma reconnect_last_fixed_endpoint_slope :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    r <> [] ->
    init (last_segment r) = term (last_segment sub) ->
    fst (term (last_segment r)) < fst (term (last_segment sub)) ->
    reconnect_slope_after l sub r h (last_segment r).
Admitted.

Lemma reconnect_head_slope_after :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    l <> [] ->
    reconnect_slope_after l sub r h (hd_segment l).
Proof.
  intros l sub r h Hne Hconn Hmono Hsparse Hl.
  destruct (classified_head_same_region
              l sub r (classify_spec l sub r Hne Hconn Hmono Hsparse) Hl)
    as [Hsame | [Hterm Hx]].
  - now apply same_region_reconnect_slope_after.
  - now apply reconnect_head_fixed_endpoint_slope.
Qed.

Lemma reconnect_last_slope_after :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    r <> [] ->
    reconnect_slope_after l sub r h (last_segment r).
Proof.
  intros l sub r h Hne Hconn Hmono Hsparse Hr.
  destruct (classified_last_same_region
              l sub r (classify_spec l sub r Hne Hconn Hmono Hsparse) Hr)
    as [Hsame | [Hinit Hx]].
  - now apply same_region_reconnect_slope_after.
  - now apply reconnect_last_fixed_endpoint_slope.
Qed.

(* 始点傾きを保存した再接続では、元の始端延長線を始点の領域に従って
   平行移動したものが新しい始端延長線になる。 *)
Lemma reconnect_one_head_extension_shift :
  forall l sub r h s p,
    reconnectable_after l sub r h s ->
    slope_init (reconnect_one l sub r h s) = slope_init s ->
    onHead s p ->
    onHead (reconnect_one l sub r h s)
      (shift h (classify l sub r (init s)) p).
Proof.
  intros l sub r h s p Hrec Hslope Hp.
  rewrite shift_as_translation.
  assert (Hinit :
      init (reconnect_one l sub r h s) =
      init (translate_seg
              (region_translation h (classify l sub r (init s))) s)).
  { rewrite reconnect_one_init by exact Hrec.
    unfold operate_point. rewrite shift_as_translation.
    symmetry. apply translate_seg_init. }
  assert (Hslope' :
      slope_init (reconnect_one l sub r h s) =
      slope_init (translate_seg
        (region_translation h (classify l sub r (init s))) s)).
  { rewrite Hslope. symmetry. apply translate_seg_slope_init. }
  apply (proj2 (head_extension_determined_by_init_slope
                  _ _ Hinit Hslope' _)).
  now apply onHead_translate.
Qed.

(* 終点傾きを保存した再接続についての末端延長線版。 *)
Lemma reconnect_one_last_extension_shift :
  forall l sub r h s p,
    reconnectable_after l sub r h s ->
    slope_term (reconnect_one l sub r h s) = slope_term s ->
    onLast s p ->
    onLast (reconnect_one l sub r h s)
      (shift h (classify l sub r (term s)) p).
Proof.
  intros l sub r h s p Hrec Hslope Hp.
  rewrite shift_as_translation.
  assert (Hterm :
      term (reconnect_one l sub r h s) =
      term (translate_seg
              (region_translation h (classify l sub r (term s))) s)).
  { rewrite reconnect_one_term by exact Hrec.
    unfold operate_point. rewrite shift_as_translation.
    symmetry. apply translate_seg_term. }
  assert (Hslope' :
      slope_term (reconnect_one l sub r h s) =
      slope_term (translate_seg
        (region_translation h (classify l sub r (term s))) s)).
  { rewrite Hslope. symmetry. apply translate_seg_slope_term. }
  apply (proj2 (last_extension_determined_by_term_slope
                  _ _ Hterm Hslope' _)).
  now apply onLast_translate.
Qed.

(* 傾き付き再接続が可能なら、始端延長線上の点も始点の分類どおり移る。 *)
Lemma reconnect_one_head_extension_operated :
  forall l sub r h s p,
    reconnect_slope_after l sub r h s ->
    onHead s p ->
    onHead (reconnect_one l sub r h s)
      (shift h (classify l sub r (init s)) p).
Proof.
  intros l sub r h s p Hslope Hp.
  apply reconnect_one_head_extension_shift; try assumption.
  - unfold reconnectable_after.
    now apply reconnect_slope_reconnectable with
      (slope_p := slope_init s) (slope_q := slope_term s).
  - now apply reconnect_one_slope_init.
Qed.

(* 終端延長線上の点についての終点版。 *)
Lemma reconnect_one_last_extension_operated :
  forall l sub r h s p,
    reconnect_slope_after l sub r h s ->
    onLast s p ->
    onLast (reconnect_one l sub r h s)
      (shift h (classify l sub r (term s)) p).
Proof.
  intros l sub r h s p Hslope Hp.
  apply reconnect_one_last_extension_shift; try assumption.
  - unfold reconnectable_after.
    now apply reconnect_slope_reconnectable with
      (slope_p := slope_init s) (slope_q := slope_term s).
  - now apply reconnect_one_slope_term.
Qed.

(* 再接続後の strict 先頭延長線点は，移動前の strict
   延長線点を先頭の分類どおりに動かしたものである。 *)
Lemma reconnect_head_strict_extension_preimage :
  forall l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    onHead_extend_strict (reconnect_split l sub r h) p ->
    exists q,
      onHead_extend_strict (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (init (hd_segment (l ++ sub ++ r)))) q.
Proof.
  intros l sub r h p Hne Hconn Hmono Hsparse Hstrict.
  destruct l as [|a l'].
  - destruct sub as [|b sub']; [contradiction|].
    assert (Hfix : classify [] (b :: sub') r (init b) = RegFix).
    { apply (classified_sub_fixed
               [] (b :: sub') r
               (classify_spec [] (b :: sub') r
                  ltac:(discriminate) Hconn Hmono Hsparse)).
      apply onSegmentlist_init_hd. discriminate. }
    exists p. split.
    + exact Hstrict.
    + simpl in Hfix |- *. now rewrite Hfix.
  - simpl in Hstrict |- *.
    destruct Hstrict as [t [Ht Hpoint]].
    change (point (reconnect_one (a :: l') sub r h a) t = p) in Hpoint.
    pose proof (reconnect_head_slope_after
                  (a :: l') sub r h Hne Hconn Hmono Hsparse
                  ltac:(discriminate)) as Hslope.
    simpl in Hslope.
    assert (Hrec : reconnectable_after (a :: l') sub r h a).
    { unfold reconnectable_after.
      now apply reconnect_slope_reconnectable with
        (slope_p := slope_init a) (slope_q := slope_term a). }
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
    { rewrite (reconnect_one_slope_init _ _ _ _ _ Hslope).
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
  forall l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    onLast_extend_strict (reconnect_split l sub r h) p ->
    exists q,
      onLast_extend_strict (l ++ sub ++ r) q
      /\ p = shift h
          (classify l sub r (term (last_segment (l ++ sub ++ r)))) q.
Proof.
  intros l sub r h p Hne Hconn Hmono Hsparse Hstrict.
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
               (classify_spec l sub [] Hne Hconn Hmono Hsparse)).
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
    pose proof (reconnect_last_slope_after
                  l sub (a :: r') h Hne Hconn Hmono Hsparse
                  ltac:(discriminate)) as Hslope.
    set (s := last_segment (a :: r')).
    change (reconnect_slope_after l sub (a :: r') h s) in Hslope.
    change (point (reconnect_one l sub (a :: r') h s) t = p) in Hpoint.
    assert (Hrec : reconnectable_after l sub (a :: r') h s).
    { unfold reconnectable_after.
      now apply reconnect_slope_reconnectable with
        (slope_p := slope_init s) (slope_q := slope_term s). }
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
    { rewrite (reconnect_one_slope_term _ _ _ _ _ Hslope).
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

Lemma reconnect_segs_app :
  forall l sub r h ls1 ls2,
    reconnect_segs l sub r h (ls1 ++ ls2) =
      reconnect_segs l sub r h ls1 ++ reconnect_segs l sub r h ls2.
Proof. intros. unfold reconnect_segs. apply map_app. Qed.

Lemma reconnect_segs_length :
  forall l sub r h ls,
    length (reconnect_segs l sub r h ls) = length ls.
Proof. intros. unfold reconnect_segs. apply length_map. Qed.

Lemma reconnect_segs_nonnil :
  forall l sub r h ls,
    ls <> [] -> reconnect_segs l sub r h ls <> [].
Proof.
  intros l sub r h ls Hne Hnil. apply Hne.
  apply length_zero_iff_nil.
  rewrite <- (reconnect_segs_length l sub r h ls), Hnil. reflexivity.
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
(*  6.  疎性と延長線を保つ再接続                                     *)
(* ================================================================= *)

(* 十分大きい移動では、各セグメントの二端点の y 座標は一致しない。 *)
Lemma operation_height_safe :
  forall l sub r h s,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    In s (l ++ sub ++ r) ->
    snd (operate_point l sub r h (init s)) <>
    snd (operate_point l sub r h (term s)).
Proof.
  intros l sub r h s Hne Hconn Hmono Hh Hsparse Hs.
  pose proof (classified_segment_endpoints_monotone
                l sub r (classify_spec l sub r Hne Hconn Hmono Hsparse)
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
    In s (l ++ sub ++ r) ->
    reconnectable_after l sub r h s.
Proof.
  intros l sub r h s Hne Hconn Hmono Hh Hsparse Hs.
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
    all_reconnectable l sub r h (l ++ sub ++ r).
Proof.
  intros l sub r h Hne Hconn Hmono Hh Hsparse s Hs.
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
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (reconnect_split l sub r h) i = Some s' ->
    orn_seg s' = orn_seg s
    /\ init s' = operate_point l sub r h (init s)
    /\ term s' = operate_point l sub r h (term s).
Proof.
  intros l sub r h i s s' Hne Hconn Hmono Hsparse Hrec Hold Hnew.
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
  eapply embed_scurve_transfer; [exact Hembed | | |].
  - unfold reconnect_split. repeat rewrite length_app.
    rewrite !reconnect_segs_length. reflexivity.
  - intros i s s' Hold Hnew.
    exact (proj1 (reconnect_split_nth_spec
                    l sub r h i s s' Hne Hconn Hmono Hsparse Hrec
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
                  l sub r h i old1 s1 Hne Hconn Hmono Hsparse Hrec E1 H1)
      as [_ [_ Hterm]].
    pose proof (reconnect_split_nth_spec
                  l sub r h (S i) old2 s2 Hne Hconn Hmono Hsparse Hrec E2 H2)
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
     rx1 (rect_of [t]) <= rx0 (rect_of [s])
  \/ rx1 (rect_of [s]) <= rx0 (rect_of [t])
  \/ ry1 (rect_of [t]) <= ry0 (rect_of [s])
  \/ ry1 (rect_of [s]) <= ry0 (rect_of [t]).

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

Lemma open_intervals_have_common_point :
  forall a0 a1 b0 b1,
    a0 < a1 -> b0 < b1 -> a0 < b1 -> b0 < a1 ->
    exists x, a0 < x < a1 /\ b0 < x < b1.
Proof.
  intros a0 a1 b0 b1 Ha Hb Hab Hba.
  exists ((Rmax a0 b0 + Rmin a1 b1) / 2).
  unfold Rmax, Rmin.
  destruct (Rle_dec a0 b0); destruct (Rle_dec a1 b1); lra.
Qed.

(* 一方の端点長方形が他方を避ければ、二長方形は軸方向に分離する。 *)
Lemma rectangles_avoid_implies_axis_separated : forall s t,
  (forall p,
    in_segment_rect_or_endpoints t p ->
    ~ in_rect_or_endpoints_at [s] p) ->
  endpoint_rectangles_axis_separated s t.
Proof.
  intros s t Havoid. unfold endpoint_rectangles_axis_separated.
  destruct (classic (rx1 (rect_of [t]) <= rx0 (rect_of [s]))) as [H | H]; [now left|].
  destruct (classic (rx1 (rect_of [s]) <= rx0 (rect_of [t]))) as [H' | H']; [now right; left|].
  destruct (classic (ry1 (rect_of [t]) <= ry0 (rect_of [s]))) as [Hy | Hy]; [now right; right; left|].
  destruct (classic (ry1 (rect_of [s]) <= ry0 (rect_of [t]))) as [Hy' | Hy']; [now right; right; right|].
  destruct (singleton_rect_positive s) as [Hsx Hsy].
  destruct (singleton_rect_positive t) as [Htx Hty].
  destruct (open_intervals_have_common_point
              (rx0 (rect_of [s])) (rx1 (rect_of [s]))
              (rx0 (rect_of [t])) (rx1 (rect_of [t]))
              Hsx Htx ltac:(lra) ltac:(lra))
    as [x [Hxs Hxt]].
  destruct (open_intervals_have_common_point
              (ry0 (rect_of [s])) (ry1 (rect_of [s]))
              (ry0 (rect_of [t])) (ry1 (rect_of [t]))
              Hsy Hty ltac:(lra) ltac:(lra))
    as [y [Hys Hyt]].
  exfalso.
  apply (Havoid (x, y)).
  - right; right. unfold in_rect. exact (conj Hxt Hyt).
  - right; right. unfold in_rect. exact (conj Hxs Hys).
Qed.

Lemma in_segment_rect_or_endpoints_closed_bounds : forall s p,
  in_segment_rect_or_endpoints s p ->
  rx0 (rect_of [s]) <= fst p <= rx1 (rect_of [s])
  /\ ry0 (rect_of [s]) <= snd p <= ry1 (rect_of [s]).
Proof.
  intros s p [Hp | [Hp | Hp]].
  - subst p. unfold rect_of; simpl. split; split;
      [apply Rmin_l | apply Rmax_l | apply Rmin_l | apply Rmax_l].
  - subst p. unfold rect_of; simpl. split; split;
      [apply Rmin_r | apply Rmax_r | apply Rmin_r | apply Rmax_r].
  - unfold in_rect in Hp. lra.
Qed.

(* 軸方向に分離した二長方形は、端点衝突さえなければ sparse の分離を満たす。 *)
Lemma axis_separated_boxes_avoid : forall s t,
  endpoint_rectangles_axis_separated s t ->
  (forall ps pt,
    endpoint_of_seg s ps -> endpoint_of_seg t pt -> ps <> pt) ->
  forall p,
    in_segment_rect_or_endpoints t p ->
    ~ in_rect_or_endpoints_at [s] p.
Proof.
  intros s t Haxis Hend p Hp Hs.
  destruct Hs as [Hs | [Hs | Hs]].
  - subst p. destruct Hp as [Hp | [Hp | Hp]].
    + apply (Hend (init s) (init t)); [now left | now left |].
      simpl in Hp. exact Hp.
    + apply (Hend (init s) (term t)); [now left | now right |].
      simpl in Hp. exact Hp.
    + change (in_rect (rect_of [t]) (init s)) in Hp.
      pose proof (in_segment_rect_or_endpoints_closed_bounds
                    s (init s) (or_introl eq_refl)) as Hsb.
      destruct Hsb as [[Hsx0 Hsx1] [Hsy0 Hsy1]].
      unfold in_rect in Hp. destruct Hp as [[Htx0 Htx1] [Hty0 Hty1]].
      unfold endpoint_rectangles_axis_separated in Haxis.
      destruct Haxis as [Haxis | [Haxis | [Haxis | Haxis]]]; lra.
  - subst p. destruct Hp as [Hp | [Hp | Hp]].
    + apply (Hend (term s) (init t)); [now right | now left |].
      simpl in Hp. exact Hp.
    + apply (Hend (term s) (term t)); [now right | now right |].
      simpl in Hp. exact Hp.
    + change (in_rect (rect_of [t]) (term s)) in Hp.
      pose proof (in_segment_rect_or_endpoints_closed_bounds s (term s)
                    (or_intror (or_introl eq_refl))) as Hsb.
      destruct Hsb as [[Hsx0 Hsx1] [Hsy0 Hsy1]].
      unfold in_rect in Hp. destruct Hp as [[Htx0 Htx1] [Hty0 Hty1]].
      unfold endpoint_rectangles_axis_separated in Haxis.
      destruct Haxis as [Haxis | [Haxis | [Haxis | Haxis]]]; lra.
  - pose proof (in_segment_rect_or_endpoints_closed_bounds t p Hp) as Htb.
    destruct Htb as [[Htx0 Htx1] [Hty0 Hty1]].
    unfold in_rect in Hs. destruct Hs as [[Hsx0 Hsx1] [Hsy0 Hsy1]].
    unfold endpoint_rectangles_axis_separated in Haxis.
    destruct Haxis as [Haxis | [Haxis | [Haxis | Haxis]]]; lra.
Qed.

(* 非隣接な旧端点は異なり、operate_point の単射性により移動後も異なる。 *)
Lemma operated_nonadjacent_endpoints_distinct :
  forall l sub r h i j s t ps pt,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    0 < h ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (l ++ sub ++ r) j = Some t ->
    (S i < j \/ S j < i)%nat ->
    endpoint_of_seg s ps ->
    endpoint_of_seg t pt ->
    operate_point l sub r h ps <> operate_point l sub r h pt.
Proof.
  intros l sub r h i j s t ps pt Hne Hconn Hmono Hsparse Hh
    Hs Ht Hfar Hps Hpt Heq.
  assert (HpEq : ps = pt).
  { eapply operate_point_injective; eauto. }
  destruct (nth_error_far_in_nonadjacent_sides
              (l ++ sub ++ r) i j s t Hs Ht Hfar)
    as [l0 [r0 [Hsplit Hin]]].
  destruct (Hsparse l0 s r0 Hsplit) as [_ Hrect].
  pose proof (Hrect t pt Hin) as Havoid.
  apply Havoid.
  - destruct Hpt as [Hpt | Hpt]; subst pt.
    + now left.
    + now right; left.
  - rewrite <- HpEq. destruct Hps as [Hps | Hps]; subst ps.
    + now left.
    + now right; left.
Qed.

(* 端点間の分類順序により、旧長方形の軸方向の分離は移動後も保たれる。 *)
Lemma operated_endpoint_rectangles_axis_separated :
  forall l sub r h i j s t s' t',
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
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
  intros l sub r h i j s t s' t' Hne Hconn Hmono Hsparse Hh
    Hs Ht Hfar Hsinit Hsterm Htinit Htterm Haxis.
  assert (Horder :
    forall i0 j0 u v pu pv,
      nth_error (l ++ sub ++ r) i0 = Some u ->
      nth_error (l ++ sub ++ r) j0 = Some v ->
      (S i0 < j0 \/ S j0 < i0)%nat ->
      endpoint_of_seg u pu -> endpoint_of_seg v pv ->
      snd pu <= snd pv ->
      snd (operate_point l sub r h pu) <=
      snd (operate_point l sub r h pv)).
  { intros i0 j0 u v pu pv Hu Hv Hfar0 Hpu Hpv Hy.
    unfold operate_point. eapply shift_preserves_vertical_order; [exact Hh | exact Hy |].
    exact (classified_nonadjacent_endpoint_order
             l sub r (classify_spec l sub r Hne Hconn Hmono Hsparse)
             i0 j0 u v pu pv Hu Hv Hfar0 Hpu Hpv Hy). }
  unfold endpoint_rectangles_axis_separated in Haxis |- *.
  destruct Haxis as [Hleft | [Hright | [Hbelow | Habove]]].
  - left.
    change (Rmax (fst (init t')) (fst (term t')) <=
            Rmin (fst (init s')) (fst (term s'))).
    change (Rmax (fst (init t)) (fst (term t)) <=
            Rmin (fst (init s)) (fst (term s))) in Hleft.
    rewrite Hsinit, Hsterm, Htinit, Htterm.
    rewrite !operate_point_fst. exact Hleft.
  - right; left.
    change (Rmax (fst (init s')) (fst (term s')) <=
            Rmin (fst (init t')) (fst (term t'))).
    change (Rmax (fst (init s)) (fst (term s)) <=
            Rmin (fst (init t)) (fst (term t))) in Hright.
    rewrite Hsinit, Hsterm, Htinit, Htterm.
    rewrite !operate_point_fst. exact Hright.
  - right; right; left.
    change (Rmax (snd (init t')) (snd (term t')) <=
            Rmin (snd (init s')) (snd (term s'))).
    rewrite Hsinit, Hsterm, Htinit, Htterm.
    change (Rmax (snd (init t)) (snd (term t)) <=
            Rmin (snd (init s)) (snd (term s))) in Hbelow.
    assert (Hold : forall pt ps,
      endpoint_of_seg t pt -> endpoint_of_seg s ps -> snd pt <= snd ps).
    { intros pt ps Hpt Hps. destruct Hpt as [-> | ->]; destruct Hps as [-> | ->];
        pose proof (Rmax_l (snd (init t)) (snd (term t)));
        pose proof (Rmax_r (snd (init t)) (snd (term t)));
        pose proof (Rmin_l (snd (init s)) (snd (term s)));
        pose proof (Rmin_r (snd (init s)) (snd (term s))); lra. }
    assert (Hfar' : (S j < i \/ S i < j)%nat) by tauto.
    apply Rmax_lub; apply Rmin_glb.
    + eapply (Horder j i t s (init t) (init s));
        [exact Ht | exact Hs | exact Hfar' | now left | now left |].
      apply Hold; now left.
    + eapply (Horder j i t s (init t) (term s));
        [exact Ht | exact Hs | exact Hfar' | now left | now right |].
      apply Hold; [now left | now right].
    + eapply (Horder j i t s (term t) (init s));
        [exact Ht | exact Hs | exact Hfar' | now right | now left |].
      apply Hold; [now right | now left].
    + eapply (Horder j i t s (term t) (term s));
        [exact Ht | exact Hs | exact Hfar' | now right | now right |].
      apply Hold; now right.
  - right; right; right.
    change (Rmax (snd (init s')) (snd (term s')) <=
            Rmin (snd (init t')) (snd (term t'))).
    rewrite Hsinit, Hsterm, Htinit, Htterm.
    change (Rmax (snd (init s)) (snd (term s)) <=
            Rmin (snd (init t)) (snd (term t))) in Habove.
    assert (Hold : forall ps pt,
      endpoint_of_seg s ps -> endpoint_of_seg t pt -> snd ps <= snd pt).
    { intros ps pt Hps Hpt. destruct Hps as [-> | ->]; destruct Hpt as [-> | ->];
        pose proof (Rmax_l (snd (init s)) (snd (term s)));
        pose proof (Rmax_r (snd (init s)) (snd (term s)));
        pose proof (Rmin_l (snd (init t)) (snd (term t)));
        pose proof (Rmin_r (snd (init t)) (snd (term t))); lra. }
    apply Rmax_lub; apply Rmin_glb.
    + eapply (Horder i j s t (init s) (init t));
        [exact Hs | exact Ht | exact Hfar | now left | now left |].
      apply Hold; now left.
    + eapply (Horder i j s t (init s) (term t));
        [exact Hs | exact Ht | exact Hfar | now left | now right |].
      apply Hold; [now left | now right].
    + eapply (Horder i j s t (term s) (init t));
        [exact Hs | exact Ht | exact Hfar | now right | now left |].
      apply Hold; [now right | now left].
    + eapply (Horder i j s t (term s) (term t));
        [exact Hs | exact Ht | exact Hfar | now right | now right |].
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
    segment_rectangles_separated (reconnect_split l sub r h).
Proof.
  intros l sub r h Hne Hconn Hmono Hh Hrec Hsparse.
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
                l sub r h i s s' Hne Hconn Hmono Hsparse Hrec Hs Hs')
    as [_ [Hsinit Hsterm]].
  pose proof (reconnect_split_nth_spec
                l sub r h j t t' Hne Hconn Hmono Hsparse Hrec Ht Ht'idx)
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
       exact (proj1 Hh) | exact Hs | exact Ht | exact Hfar |
       exact Hsinit | exact Hsterm | exact Htinit | exact Htterm |
       exact HoldAxis]. }
  apply (axis_separated_boxes_avoid s' t' HnewAxis); [|exact Hp].
  assert (HendOld : forall ps pt,
    endpoint_of_seg s ps -> endpoint_of_seg t pt ->
    operate_point l sub r h ps <> operate_point l sub r h pt).
  { intros ps pt Hps Hpt.
    eapply (operated_nonadjacent_endpoints_distinct
              l sub r h i j s t ps pt);
      [exact Hne | exact Hconn | exact Hmono | exact Hsparse |
       exact (proj1 Hh) | exact Hs | exact Ht | exact Hfar |
       exact Hps | exact Hpt]. }
  intros ps' pt' Hps' Hpt'.
  destruct Hps' as [Hps' | Hps']; destruct Hpt' as [Hpt' | Hpt'];
    subst ps' pt'.
  - rewrite Hsinit, Htinit. apply HendOld; now left.
  - rewrite Hsinit, Htterm. apply HendOld; [now left | now right].
  - rewrite Hsterm, Htinit. apply HendOld; [now right | now left].
  - rewrite Hsterm, Htterm. apply HendOld; now right.
Qed.

(* 再接続後の先頭・末尾延長線は、各セグメントの端点長方形を避ける。 *)
Lemma reconnect_preserves_extensions_avoid_rectangles :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    sparse_embedding (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    extensions_avoid_segment_rectangles (reconnect_split l sub r h).
Admitted.

(* 平行移動後の二つの延長線が交わらない *)
Lemma classified_extension_shifts_disjoint :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    sparse_embedding (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    (l <> [] -> reconnect_slope_after l sub r h (hd_segment l)) ->
    (r <> [] -> reconnect_slope_after l sub r h (last_segment r)) ->
    extensions_disjoint (reconnect_split l sub r h).
Admitted.

(* 先頭・末尾は make_seg_slope で傾きを保存するため、両延長線を保てる。 *)
Lemma reconnect_preserves_extensions_disjoint :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    sparse_embedding (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    extensions_disjoint (reconnect_split l sub r h).
Proof.
  intros l sub r h Hne Hconn Hmono Hh Hrec Hsparse Hext.
  apply classified_extension_shifts_disjoint; try assumption.
  - intros Hl. now apply reconnect_head_slope_after.
  - intros Hr. now apply reconnect_last_slope_after.
Qed.

(* 再接続後の非隣接長方形と strict 延長線の分離から、
   新しい全域疎性を組み立てる。 *)
Lemma reconnect_preserves_sparse :
  forall l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    sparse_embedding (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    sparse_embedding (reconnect_split l sub r h).
Proof.
  intros l sub r h Hne Hconn Hmono Hh Hrec Hsparse Hext.
  assert (Hrect :
      segment_rectangles_separated (reconnect_split l sub r h)).
  { now apply reconnect_preserves_segment_rectangles_separated. }
  assert (HextRect :
      extensions_avoid_segment_rectangles (reconnect_split l sub r h)).
  { now apply reconnect_preserves_extensions_avoid_rectangles. }
  apply geometric_sparse_embedding.
  - exact Hrect.
  - exact HextRect.
Qed.

Definition both_left_of_sub (sub : list Segment) (p q : Point) : Prop :=
  fst p <= rx0 (rect_of sub) /\ fst q <= rx0 (rect_of sub).

Definition both_right_of_sub (sub : list Segment) (p q : Point) : Prop :=
  rx1 (rect_of sub) <= fst p /\ rx1 (rect_of sub) <= fst q.

Definition both_above_of_sub (sub : list Segment) (p q : Point) : Prop :=
  ry1 (bbox_of sub) <= snd p /\ ry1 (bbox_of sub) <= snd q.

Definition both_below_of_sub (sub : list Segment) (p q : Point) : Prop :=
  snd p <= ry0 (bbox_of sub) /\ snd q <= ry0 (bbox_of sub).

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

(* 左右の同じ側に固まらない二端点の x 区間は、sub の x 区間と
   内部で共通する。 *)
Lemma nonhorizontal_sides_have_common_x :
  forall sub s,
    sub <> [] -> connected sub -> x_monotone_segs sub ->
    ~ both_left_of_sub sub (init s) (term s) ->
    ~ both_right_of_sub sub (init s) (term s) ->
    exists x,
      rx0 (rect_of sub) < x < rx1 (rect_of sub)
      /\ rx0 (rect_of [s]) < x < rx1 (rect_of [s]).
Proof.
  intros sub s Hne Hconn Hmono Hleft Hright.
  pose proof (sub_rect_has_positive_width sub Hne Hconn Hmono) as Hsub.
  pose proof (segment_rect_has_positive_width s) as Hseg.
  assert (HcrossL : rx0 (rect_of sub) < rx1 (rect_of [s])).
  { apply Rnot_le_lt. intro Hle. apply Hleft.
    unfold both_left_of_sub, rect_of in *; simpl in *.
    split.
    - eapply Rle_trans; [apply Rmax_l | exact Hle].
    - eapply Rle_trans; [apply Rmax_r | exact Hle]. }
  assert (HcrossR : rx0 (rect_of [s]) < rx1 (rect_of sub)).
  { apply Rnot_le_lt. intro Hle. apply Hright.
    unfold both_right_of_sub, rect_of in *; simpl in *.
    split.
    - eapply Rle_trans; [exact Hle | apply Rmin_l].
    - eapply Rle_trans; [exact Hle | apply Rmin_r]. }
  now apply open_intervals_have_common_point.
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
    rx0 (rect_of [s]) < fst q < rx1 (rect_of [s]) ->
    snd q < snd p ->
    ry0 (bbox_of sub) <= snd (init s)
    /\ ry0 (bbox_of sub) <= snd (term s).
Proof.
  intros l sub r s p q Hsparse Hs Hp Hq Hqx Hy.
  pose proof (bbox_of_bounds sub q Hq) as [Hqlo _].
  pose proof (segment_in_rect_or_endpoints s p Hp) as Hpbox.
  assert (Hpy : Rmin (snd (init s)) (snd (term s)) <= snd p
                <= Rmax (snd (init s)) (snd (term s))).
  { destruct Hpbox as [-> | [-> | Hpbox]].
    - split; [apply Rmin_l | apply Rmax_l].
    - split; [apply Rmin_r | apply Rmax_r].
    - unfold in_rect in Hpbox. destruct Hpbox as [_ HpY].
      change (Rmin (snd (init s)) (snd (term s)) < snd p <
              Rmax (snd (init s)) (snd (term s))) in HpY.
      lra. }
  assert (Havoid := sparse_nonadjacent_box_avoids_sub_points
                       l sub r s q Hsparse Hs Hq).
  split; apply Rnot_lt_le; intro Hend.
  - apply Havoid. right; right. unfold in_rect. split; [exact Hqx |].
    change (Rmin (snd (init s)) (snd (term s)) < snd q <
            Rmax (snd (init s)) (snd (term s))).
    destruct Hpy as [Hpy0 Hpy1].
    split.
    + eapply Rle_lt_trans; [apply Rmin_l |]. lra.
    + lra.
  - apply Havoid. right; right. unfold in_rect. split; [exact Hqx |].
    change (Rmin (snd (init s)) (snd (term s)) < snd q <
            Rmax (snd (init s)) (snd (term s))).
    destruct Hpy as [Hpy0 Hpy1].
    split.
    + eapply Rle_lt_trans; [apply Rmin_r |]. lra.
    + lra.
Qed.

(* 下側の場合の双対。両端とも bbox の上端以下にある。 *)
Lemma below_sub_point_bounds_segment_endpoints :
  forall l sub r s p q,
    sparse_embedding (l ++ sub ++ r) ->
    In s (nonadjacent_sides l r) ->
    onSegment s p ->
    onSegmentlist sub q ->
    rx0 (rect_of [s]) < fst q < rx1 (rect_of [s]) ->
    snd p < snd q ->
    snd (init s) <= ry1 (bbox_of sub)
    /\ snd (term s) <= ry1 (bbox_of sub).
Proof.
  intros l sub r s p q Hsparse Hs Hp Hq Hqx Hy.
  pose proof (bbox_of_bounds sub q Hq) as [_ Hqhi].
  pose proof (segment_in_rect_or_endpoints s p Hp) as Hpbox.
  assert (Hpy : Rmin (snd (init s)) (snd (term s)) <= snd p
                <= Rmax (snd (init s)) (snd (term s))).
  { destruct Hpbox as [-> | [-> | Hpbox]].
    - split; [apply Rmin_l | apply Rmax_l].
    - split; [apply Rmin_r | apply Rmax_r].
    - unfold in_rect in Hpbox. destruct Hpbox as [_ HpY].
      change (Rmin (snd (init s)) (snd (term s)) < snd p <
              Rmax (snd (init s)) (snd (term s))) in HpY.
      lra. }
  assert (Havoid := sparse_nonadjacent_box_avoids_sub_points
                       l sub r s q Hsparse Hs Hq).
  split; apply Rnot_lt_le; intro Hend.
  - apply Havoid. right; right. unfold in_rect. split; [exact Hqx |].
    change (Rmin (snd (init s)) (snd (term s)) < snd q <
            Rmax (snd (init s)) (snd (term s))).
    destruct Hpy as [Hpy0 Hpy1].
    split.
    + lra.
    + eapply Rlt_le_trans; [| apply Rmax_l]. lra.
  - apply Havoid. right; right. unfold in_rect. split; [exact Hqx |].
    change (Rmin (snd (init s)) (snd (term s)) < snd q <
            Rmax (snd (init s)) (snd (term s))).
    destruct Hpy as [Hpy0 Hpy1].
    split.
    + lra.
    + eapply Rlt_le_trans; [| apply Rmax_r]. lra.
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
    In s (nonadjacent_sides l r) ->
    endpoint_box_separated_from_sub sub
      (operate_point l sub r h (init s))
      (operate_point l sub r h (term s)).
Proof.
  intros l sub r h s Hne Hconn Hmono Hh Hsparse Hs.
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
                    (classify_spec l sub r Hne Hconn Hmono Hsparse)
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
          rx0 (rect_of [s]) < fst q < rx1 (rect_of [s])) by lra.
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

(* 元の sparse 性により、非隣接セグメントの端点は sub の両端点と
   一致しない。 *)
Lemma sparse_nonadjacent_endpoint_avoids_sub_endpoints :
  forall l sub r s p,
    sub <> [] ->
    sparse_embedding (l ++ sub ++ r) ->
    In s (nonadjacent_sides l r) ->
    endpoint_of_seg s p ->
    p <> init (hd_segment sub) /\ p <> term (last_segment sub).
Proof.
  intros l sub r s p Hne Hsparse Hs Hp.
  destruct sub as [|first tail]; [contradiction|].
  assert (HfirstEq :
      l ++ first :: tail ++ r = l ++ [first] ++ (tail ++ r)) by
    (repeat rewrite <- app_assoc; reflexivity).
  pose proof (Hsparse l first (tail ++ r) HfirstEq) as HfirstSparse.
  assert (HsFirst : In s (nonadjacent_sides l (tail ++ r))).
  { now apply nonadjacent_sides_extend_right. }
  assert (HpBox : in_segment_rect_or_endpoints s p).
  { destruct Hp as [-> | ->]; [now left | now right; left]. }
  assert (HavoidFirst : ~ in_rect_or_endpoints_at [first] p).
  { exact ((proj2 HfirstSparse) s p HsFirst HpBox). }
  split.
  - unfold hd_segment. simpl. intro Heq. apply HavoidFirst.
    left. exact Heq.
  - assert (HlistNe : first :: tail <> []) by discriminate.
    destruct (exists_last HlistNe) as [prefix [last Hdecomp]].
    assert (HfullEq :
        l ++ first :: tail ++ r =
        (l ++ prefix) ++ [last] ++ r).
    { transitivity (l ++ (prefix ++ [last]) ++ r).
      - exact (f_equal (fun xs => l ++ xs ++ r) Hdecomp).
      - repeat rewrite app_assoc. reflexivity. }
    pose proof (Hsparse (l ++ prefix) last r HfullEq) as HlastSparse.
    assert (HsLast : In s (nonadjacent_sides (l ++ prefix) r)).
    { now apply nonadjacent_sides_extend_left. }
    assert (HavoidLast : ~ in_rect_or_endpoints_at [last] p).
    { exact ((proj2 HlastSparse) s p HsLast HpBox). }
    rewrite Hdecomp, (last_app_nonnil prefix [last]) by discriminate.
    unfold last_segment at 1. simpl. intro Heq. apply HavoidLast.
    right; left. exact Heq.
Qed.

(* sub の端点は固定され、operate_point は単射なので、移動後にも
   非隣接セグメントの端点とは衝突しない。 *)
Lemma operated_nonadjacent_endpoint_avoids_sub_endpoints :
  forall l sub r h s p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    0 < h ->
    In s (nonadjacent_sides l r) ->
    endpoint_of_seg s p ->
    operate_point l sub r h p <> init (hd_segment sub)
    /\ operate_point l sub r h p <> term (last_segment sub).
Proof.
  intros l sub r h s p Hne Hconn Hmono Hsparse Hh Hs Hp.
  pose proof (sparse_nonadjacent_endpoint_avoids_sub_endpoints
                l sub r s p Hne Hsparse Hs Hp) as [Hinit Hterm].
  split; intro Heq.
  - apply Hinit.
    apply (operate_point_injective
             l sub r h p (init (hd_segment sub))
             Hne Hconn Hmono Hsparse Hh).
    rewrite Heq. symmetry. apply operate_sub_endpoint; try assumption.
    exists (hd_segment sub). split.
    + destruct sub; [contradiction | now left].
    + now left.
  - apply Hterm.
    apply (operate_point_injective
             l sub r h p (term (last_segment sub))
             Hne Hconn Hmono Hsparse Hh).
    rewrite Heq. symmetry. apply operate_sub_endpoint; try assumption.
    exists (last_segment sub). split.
    + apply last_In. exact Hne.
    + now right.
Qed.

Lemma in_rect_or_endpoints_at_closed_bounds :
  forall old p,
    in_rect_or_endpoints_at old p ->
    rx0 (rect_of old) <= fst p <= rx1 (rect_of old)
    /\ ry0 (rect_of old) <= snd p <= ry1 (rect_of old).
Proof.
  intros old p [Hp | [Hp | Hp]].
  - subst p. unfold rect_of; simpl. split; split.
    + apply Rmin_l.
    + apply Rmax_l.
    + apply Rmin_l.
    + apply Rmax_l.
  - subst p. unfold rect_of; simpl. split; split.
    + apply Rmin_r.
    + apply Rmax_r.
    + apply Rmin_r.
    + apply Rmax_r.
  - unfold in_rect in Hp. lra.
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

Lemma separated_endpoint_box_interior_neq_sub_point :
  forall sub s p q,
    endpoint_box_separated_from_sub sub (init s) (term s) ->
    rx0 (rect_of sub) <= fst q <= rx1 (rect_of sub) ->
    ry0 (bbox_of sub) <= snd q <= ry1 (bbox_of sub) ->
    in_rect (rect_of [s]) p ->
    p <> q.
Proof.
  intros sub s p q Hsep Hqx Hqy Hp Heq. subst p.
  unfold in_rect in Hp. destruct Hp as [[Hpx0 Hpx1] [Hpy0 Hpy1]].
  destruct Hsep as [Habove | [Hbelow | [Hleft | Hright]]].
  - unfold both_above_of_sub in Habove. destruct Habove as [Hi Ht].
    unfold rect_of in Hpy0, Hpy1; simpl in Hpy0, Hpy1.
    assert (Hmin : ry1 (bbox_of sub) <=
        Rmin (snd (init s)) (snd (term s))) by
      (apply Rmin_glb; assumption).
    apply (Rlt_irrefl (snd q)).
    eapply Rle_lt_trans.
    + eapply Rle_trans; [exact (proj2 Hqy) | exact Hmin].
    + exact Hpy0.
  - unfold both_below_of_sub in Hbelow. destruct Hbelow as [Hi Ht].
    unfold rect_of in Hpy0, Hpy1; simpl in Hpy0, Hpy1.
    assert (Hmax : Rmax (snd (init s)) (snd (term s)) <=
        ry0 (bbox_of sub)) by
      (apply Rmax_lub; assumption).
    apply (Rlt_irrefl (snd q)).
    eapply Rlt_le_trans.
    + exact Hpy1.
    + eapply Rle_trans; [exact Hmax | exact (proj1 Hqy)].
  - unfold both_left_of_sub in Hleft. destruct Hleft as [Hi Ht].
    unfold rect_of in Hpx0, Hpx1; simpl in Hpx0, Hpx1.
    assert (Hmax : Rmax (fst (init s)) (fst (term s)) <=
        rx0 (rect_of sub)) by
      (apply Rmax_lub; assumption).
    apply (Rlt_irrefl (fst q)).
    eapply Rlt_le_trans.
    + exact Hpx1.
    + eapply Rle_trans; [exact Hmax | exact (proj1 Hqx)].
  - unfold both_right_of_sub in Hright. destruct Hright as [Hi Ht].
    unfold rect_of in Hpx0, Hpx1; simpl in Hpx0, Hpx1.
    assert (Hmin : rx1 (rect_of sub) <=
        Rmin (fst (init s)) (fst (term s))) by
      (apply Rmin_glb; assumption).
    apply (Rlt_irrefl (fst q)).
    eapply Rle_lt_trans.
    + eapply Rle_trans; [exact (proj2 Hqx) | exact Hmin].
    + exact Hpx0.
Qed.

(* 二端点の長方形が sub の上下左右のいずれかに離れていれば、
   その中に収まるセグメントも sub の長方形と両端点を避ける。 *)
Lemma separated_endpoint_box_avoids_sub :
  forall sub s p,
    sub <> [] ->
    endpoint_box_separated_from_sub sub (init s) (term s) ->
    p <> init (hd_segment sub) ->
    p <> term (last_segment sub) ->
    in_segment_rect_or_endpoints s p ->
    ~ in_rect_or_endpoints_at sub p.
Proof.
  intros sub s p Hne Hsep Hinit Hterm Hp Hsub.
  destruct Hsub as [Hsub | [Hsub | Hsub]].
  - now apply Hinit.
  - now apply Hterm.
  - pose proof (in_segment_rect_or_endpoints_closed_bounds s p Hp)
      as [[Hpx0 Hpx1] [Hpy0 Hpy1]].
    unfold in_rect in Hsub.
    destruct Hsub as [[Hsx0 Hsx1] [Hsy0' Hsy1']].
    assert (HsubAt : in_rect_or_endpoints_at sub p) by now right; right.
    pose proof (in_sub_rect_or_endpoints_bbox_y sub p Hne HsubAt)
      as [Hsy0 Hsy1].
    pose proof (bbox_of_bounds sub (init (hd_segment sub))
                  (onSegmentlist_init_hd sub Hne)) as [HbboxInit0 HbboxInit1].
    pose proof (bbox_of_bounds sub (term (last_segment sub))
                  (onSegmentlist_term_last sub Hne)) as [HbboxTerm0 HbboxTerm1].
    assert (HrectBottom :
        ry0 (bbox_of sub) <= ry0 (rect_of sub)).
    { unfold rect_of; simpl. apply Rmin_glb; lra. }
    assert (HrectTop :
        ry1 (rect_of sub) <= ry1 (bbox_of sub)).
    { unfold rect_of; simpl. apply Rmax_lub; lra. }
    destruct Hsep as [Habove | [Hbelow | [Hleft | Hright]]].
    + unfold both_above_of_sub in Habove.
      destruct Habove as [Hinit' Hterm'].
      assert (Hmin : ry1 (bbox_of sub) <= ry0 (rect_of [s])).
      { change (ry1 (bbox_of sub) <= Rmin (snd (init s)) (snd (term s))).
        unfold Rmin.
        destruct (Rle_dec (snd (init s)) (snd (term s))); lra. }
      lra.
    + unfold both_below_of_sub in Hbelow.
      destruct Hbelow as [Hinit' Hterm'].
      assert (Hmax : ry1 (rect_of [s]) <= ry0 (bbox_of sub)).
      { change (Rmax (snd (init s)) (snd (term s)) <= ry0 (bbox_of sub)).
        unfold Rmax.
        destruct (Rle_dec (snd (init s)) (snd (term s))); lra. }
      lra.
    + unfold both_left_of_sub in Hleft.
      destruct Hleft as [Hinit' Hterm'].
      assert (Hmax : rx1 (rect_of [s]) <= rx0 (rect_of sub)).
      { change (Rmax (fst (init s)) (fst (term s)) <= rx0 (rect_of sub)).
        unfold Rmax.
        destruct (Rle_dec (fst (init s)) (fst (term s))); lra. }
      lra.
    + unfold both_right_of_sub in Hright.
      destruct Hright as [Hinit' Hterm'].
      assert (Hmin : rx1 (rect_of sub) <= rx0 (rect_of [s])).
      { change (rx1 (rect_of sub) <= Rmin (fst (init s)) (fst (term s))).
        unfold Rmin.
        destruct (Rle_dec (fst (init s)) (fst (term s))); lra. }
      lra.
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
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    In s (nonadjacent_sides l r) ->
    forall p,
      in_segment_rect_or_endpoints (reconnect_one l sub r h s) p ->
      ~ in_rect_or_endpoints_at sub p.
Proof.
  intros l sub r h s Hne Hconn Hmono Hh Hsparse Hrec Hs p Hp.
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
  assert (HavoidEnds :
      p <> init (hd_segment sub) /\ p <> term (last_segment sub)).
  { destruct Hp as [Hp | [Hp | Hp]].
    - subst p. rewrite (reconnect_one_init l sub r h s HrecOne).
      apply operated_nonadjacent_endpoint_avoids_sub_endpoints
        with (s := s); try assumption.
      + exact (proj1 Hh).
      + now left.
    - subst p. rewrite (reconnect_one_term l sub r h s HrecOne).
      apply operated_nonadjacent_endpoint_avoids_sub_endpoints
        with (s := s); try assumption.
      + exact (proj1 Hh).
      + now right.
    - split.
      + eapply separated_endpoint_box_interior_neq_sub_point;
          [exact Hsep | | | exact Hp].
        * unfold rect_of; simpl. split; [apply Rmin_l | apply Rmax_l].
        * apply bbox_of_bounds. apply onSegmentlist_init_hd. exact Hne.
      + eapply separated_endpoint_box_interior_neq_sub_point;
          [exact Hsep | | | exact Hp].
        * unfold rect_of; simpl. split; [apply Rmin_r | apply Rmax_r].
        * apply bbox_of_bounds. apply onSegmentlist_term_last. exact Hne. }
  apply (separated_endpoint_box_avoids_sub
           sub (reconnect_one l sub r h s) p Hne).
  - exact Hsep.
  - exact (proj1 HavoidEnds).
  - exact (proj2 HavoidEnds).
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
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    In s (nonadjacent_sides
            (reconnect_segs l sub r h l)
            (reconnect_segs l sub r h r)) ->
    in_segment_rect_or_endpoints s p ->
    ~ in_rect_or_endpoints_at sub p.
Proof.
  intros l sub r h s' p Hne Hconn Hmono Hh Hsparse Hrec Hs' Hp.
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
    (onHead_extend_strict (l ++ sub ++ r) q
     \/ onLast_extend_strict (l ++ sub ++ r) q) ->
    (g = RegUp -> forall z,
      fst q = fst z -> snd q < snd z -> classify l sub r z = RegUp) ->
    (g = RegDown -> forall z,
      fst q = fst z -> snd z < snd q -> classify l sub r z = RegDown) ->
    (rx0 (rect_of sub) < fst q < rx1 (rect_of sub) ->
      g = RegUp \/ g = RegDown) ->
    p = shift h g q ->
    ~ in_rect_or_endpoints_at sub p.
Proof.
  intros l sub r h p q g Hne Hconn Hmono Hh Hsparse Hqextend
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
                l sub r (classify_spec l sub r Hne Hconn Hmono Hsparse)
                z Hz) as Hzfix.
  destruct g.
  - simpl in Hshift. subst p.
    destruct HpSub as [Hinit | [Hterm | Hin]].
    + subst q. eapply sparse_strict_extension_avoids_sub_point; eauto.
      apply onSegmentlist_init_hd. exact Hne.
    + subst q. eapply sparse_strict_extension_avoids_sub_point; eauto.
      apply onSegmentlist_term_last. exact Hne.
    + destruct (Hinside ltac:(unfold in_rect in Hin; lra)); discriminate.
  - assert (Hqz : snd q < snd z).
    { pose proof (f_equal snd Hshift) as Hyshift.
      simpl in Hyshift. unfold h_large, rect_height in Hh. lra. }
    pose proof (Habove eq_refl z ltac:(lra) Hqz) as Hzup.
    congruence.
  - assert (Hzq : snd z < snd q).
    { pose proof (f_equal snd Hshift) as Hyshift.
      simpl in Hyshift. unfold h_large, rect_height in Hh. lra. }
    pose proof (Hbelow eq_refl z ltac:(lra) Hzq) as Hzdown.
    congruence.
Qed.

(* 延長線についても、十分大きな移動後に
   sub の長方形を避ける *)
Lemma reconnect_extensions_avoid_sub_rect :
  forall l sub r h p,
    connected (l ++ sub ++ r) ->
    well_split l sub r ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    (onHead_extend_strict (reconnect_split l sub r h) p
     \/ onLast_extend_strict (reconnect_split l sub r h) p) ->
    ~ in_rect_or_endpoints_at sub p.
Proof.
  intros l sub r h p Hconn Hws Hh Hsparse Hextend.
  destruct Hws as [Hne [Hmono _]].
  assert (HconnSub : connected sub).
  { eapply connected_middle. exact Hconn. }
  destruct Hextend as [Hhead | Hlast].
  - destruct (reconnect_head_strict_extension_preimage
                l sub r h p Hne HconnSub Hmono Hsparse Hhead)
      as [q [Hq Hshift]].
    set (g := classify l sub r
                (init (hd_segment (l ++ sub ++ r)))).
    eapply (classified_shifted_extension_avoids_sub_rect
              l sub r h p q g Hne HconnSub Hmono Hh Hsparse).
    + now left.
    + intros Hg z Hx Hy.
      apply (classified_above_head_up
               l sub r (classify_spec l sub r Hne HconnSub Hmono Hsparse)
               ltac:(exact Hg) z).
      exists q. split.
      * unfold onHead_extend_strict in Hq.
        unfold onHead_extend. destruct Hq as [t [Ht Hpoint]].
        exists t. split; [lra | exact Hpoint].
      * tauto.
    + intros Hg z Hx Hy.
      apply (classified_below_head_down
               l sub r (classify_spec l sub r Hne HconnSub Hmono Hsparse)
               ltac:(exact Hg) z).
      exists q. split.
      * unfold onHead_extend_strict in Hq.
        unfold onHead_extend. destruct Hq as [t [Ht Hpoint]].
        exists t. split; [lra | exact Hpoint].
      * tauto.
    + intros Hx.
      exact (classified_head_extension_at_sub_x
               l sub r (classify_spec l sub r Hne HconnSub Hmono Hsparse)
               q Hq Hx).
    + exact Hshift.
  - destruct (reconnect_last_strict_extension_preimage
                l sub r h p Hne HconnSub Hmono Hsparse Hlast)
      as [q [Hq Hshift]].
    set (g := classify l sub r
                (term (last_segment (l ++ sub ++ r)))).
    eapply (classified_shifted_extension_avoids_sub_rect
              l sub r h p q g Hne HconnSub Hmono Hh Hsparse).
    + now right.
    + intros Hg z Hx Hy.
      apply (classified_above_last_up
               l sub r (classify_spec l sub r Hne HconnSub Hmono Hsparse)
               ltac:(exact Hg) z).
      exists q. split.
      * unfold onLast_extend_strict in Hq.
        unfold onLast_extend. destruct Hq as [t [Ht Hpoint]].
        exists t. split; [lra | exact Hpoint].
      * tauto.
    + intros Hg z Hx Hy.
      apply (classified_below_last_down
               l sub r (classify_spec l sub r Hne HconnSub Hmono Hsparse)
               ltac:(exact Hg) z).
      exists q. split.
      * unfold onLast_extend_strict in Hq.
        unfold onLast_extend. destruct Hq as [t [Ht Hpoint]].
        exists t. split; [lra | exact Hpoint].
      * tauto.
    + intros Hx.
      exact (classified_last_extension_at_sub_x
               l sub r (classify_spec l sub r Hne HconnSub Hmono Hsparse)
               q Hq Hx).
    + exact Hshift.
Qed.

(* 外側の実セグメントと両延長線の退避を outside_sub 全体へまとめる。 *)
Lemma h_large_reconnect_avoids_sub_rect :
  forall l sub r h,
    connected (l ++ sub ++ r) ->
    well_split l sub r ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    forall p,
      outside_sub
        (reconnect_segs l sub r h l)
        sub
        (reconnect_segs l sub r h r) p ->
      ~ in_rect_or_endpoints_at sub p.
Proof.
  intros l sub r h Hconn Hws Hh Hsparse p Houtside.
  pose proof Hws as [Hsubne [Hmono _]].
  assert (HconnSub : connected sub).
  { eapply connected_middle. exact Hconn. }
  pose proof (operate_endpoints_reconnectable
                l sub r h Hsubne HconnSub Hmono Hh Hsparse) as Hrec.
  unfold outside_sub in Houtside.
  destruct Houtside as [Hhead | [Hsides | Hlast]].
  - apply (reconnect_extensions_avoid_sub_rect
             l sub r h p Hconn Hws Hh Hsparse).
    now left.
  - destruct Hsides as [s [Hs Hp]].
    apply (reconnect_sides_avoid_sub_rect
             l sub r h s p Hsubne HconnSub Hmono Hh Hsparse Hrec Hs).
    now apply segment_in_rect_or_endpoints.
  - apply (reconnect_extensions_avoid_sub_rect
             l sub r h p Hconn Hws Hh Hsparse).
    now right.
Qed.

(* 全域疎性とは別に、固定した sub 全体の長方形から左右を退避させる。 *)
Lemma reconnect_gives_sparse_around :
  forall l sub r h,
    connected (l ++ sub ++ r) ->
    well_split l sub r ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    sparse_around
      (reconnect_segs l sub r h l)
      sub
      (reconnect_segs l sub r h r).
Proof.
  intros l sub r h Hconn Hws Hh Hsparse.
  pose proof Hws as [Hsubne [Hmono _]].
  assert (HconnSub : connected sub).
  { eapply connected_middle. exact Hconn. }
  pose proof (operate_endpoints_reconnectable
                l sub r h Hsubne HconnSub Hmono Hh Hsparse) as Hrec.
  split.
  - intros p Hextend.
    apply (reconnect_extensions_avoid_sub_rect
             l sub r h p Hconn Hws Hh Hsparse).
    exact Hextend.
  - intros s p Hs Hp.
    exact (reconnect_sides_avoid_sub_rect
             l sub r h s p Hsubne HconnSub Hmono Hh
             Hsparse Hrec Hs Hp).
Qed.

Lemma reconnect_preserves_open :
  forall ds l sub r h,
    h_large h sub ->
    sub <> [] ->
    x_monotone_segs sub ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    sparse_embedding (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    ~ close (reconnect_split l sub r h).
Proof.
  intros ds l sub r h Hh Hne Hmono Hrec Hembed Hsparse Hext.
  assert (HconnSub : connected sub).
  { apply connected_middle with (l := l) (r := r).
    now apply embed_listDir_connected with (ds := ds). }
  apply sparse_extensions_open with (ds := ds).
  - unfold reconnect_split. intro Hnil.
    apply app_eq_nil in Hnil as [_ Htail].
    apply app_eq_nil in Htail as [Hsubnil _].
    contradiction.
  - now apply reconnect_split_preserves_embed.
  - now apply reconnect_preserves_sparse.
  - now apply reconnect_preserves_extensions_disjoint.
Qed.

(* 全域疎性の保存と sub 周りの局所疎性を一つの sparse にまとめる。 *)
Lemma reconnect_gives_sparse :
  forall l sub r h,
    connected (l ++ sub ++ r) ->
    well_split l sub r ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    sparse
      (reconnect_segs l sub r h l)
      sub
      (reconnect_segs l sub r h r).
Proof.
  intros l sub r h Hconn Hws Hh Hsparse Hext.
  pose proof Hws as [Hsubne [Hmono _]].
  assert (HconnSub : connected sub).
  { eapply connected_middle. exact Hconn. }
  pose proof (operate_endpoints_reconnectable
                l sub r h Hsubne HconnSub Hmono Hh Hsparse) as Hrec.
  unfold sparse, reconnect_split. split.
  - now apply reconnect_preserves_sparse.
  - now apply reconnect_gives_sparse_around.
Qed.


(* ================================================================= *)
(*  7.  最終命題                                                     *)
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
   /\ sparse l' sub' r'
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
                l1 sub1 r1 h Hsub1ne HconnSub1 Hx1 Hh Hsparse1) as HrecAll1.
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
      apply reconnect_preserves_open
        with (ds := ds1 ++ sub_ds ++ ds2).
      * exact Hh.
      * exact Hsub1ne.
      * exact Hx1.
      * exact HrecAll1.
      * exact Hall1.
      * exact Hsparse1.
      * exact Hext1.
    + split.
      * apply reconnect_gives_sparse; assumption.
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
    /\ sparse l sub_ls r.
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
