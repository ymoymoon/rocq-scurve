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

(* p が l ++ sub ++ r の sub 以外の部分から来ることを表す。
   点集合の差 [~ onSegmentlist sub p] では、他セグメントとの交点も
   sub 上の点として除外されてしまうため、点の由来を分解で記録する。 *)
(* 注意 : sub の端点は「外側」とみなす→ sparse 側で対処が必要 *)
Definition outside_sub (l sub r : list Segment) (p : Point) : Prop :=
  let ls := l ++ sub ++ r in
  onHead_extend ls p
  \/ onSegmentlist (l ++ r) p
  \/ onLast_extend ls p.

(* sub の両端点は、曲線の他の部分と交わらない．
    outside_sub が端点の情報を消してしまうので，こちらで拾う *)
Definition sub_endpoints_do_not_cross (l sub r : list Segment) : Prop :=
  forall t1 t2,
    t1 <> t2 ->
    (extend (l ++ sub ++ r) t1 = init (hd_segment sub)
     \/ extend (l ++ sub ++ r) t1 = term (last_segment sub)) ->
    extend (l ++ sub ++ r) t1 <> extend (l ++ sub ++ r) t2.

Lemma open_sub_endpoints_do_not_cross : forall l sub r,
  ~ close (l ++ sub ++ r) -> sub_endpoints_do_not_cross l sub r.
Proof.
  intros l sub r Hopen t1 t2 Hneq _. intro Heq.
  apply Hopen. now exists t1, t2.
Qed.

(* 全体の両端延長線、外側セグメントの端点長方形、sub の端点を分離する。 *)
Definition sparse_around (l sub r : list Segment) : Prop :=
  (forall p,
     (onHead_extend (l ++ sub ++ r) p
      \/ onLast_extend (l ++ sub ++ r) p) ->
     ~ in_rect (rect_of sub) p)
  /\ (forall s p,
        In s (l ++ r) ->
        in_segment_rect_or_endpoints s p ->
        ~ in_rect (rect_of sub) p)
  /\ sub_endpoints_do_not_cross l sub r.

(* 旧来の [outside_sub] 形式は、上の三つの分離条件から導ける。 *)
Lemma sparse_around_outside_avoids : forall l sub r p,
  sparse_around l sub r ->
  outside_sub l sub r p ->
  ~ in_rect (rect_of sub) p.
Proof.
  intros l sub r p [Hextend [Hrect Hend]] Houtside.
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
  intros l sub r p [_ Haround] Houtside.
  now apply (sparse_around_outside_avoids l sub r p Haround).
Qed.

(* 各セグメントを端点長方形で覆ったとき、異なるセグメントの
   長方形（端点を含む）が対象セグメントの開長方形へ入らない。 *)
Definition segment_rectangles_separated (ls : list Segment) : Prop :=
  forall l s r,
    ls = l ++ [s] ++ r ->
    forall t, In t (l ++ r) ->
    forall p,
      in_segment_rect_or_endpoints t p ->
      ~ in_rect (rect_of [s]) p.

Definition extensions_avoid_segment_rectangles (ls : list Segment) : Prop :=
  forall l s r,
    ls = l ++ [s] ++ r ->
    forall p,
      (onHead_extend ls p \/ onLast_extend ls p) ->
      ~ in_rect (rect_of [s]) p.

Definition segment_endpoints_separated (ls : list Segment) : Prop :=
  forall l s r,
    ls = l ++ [s] ++ r ->
    sub_endpoints_do_not_cross l [s] r.

Lemma sparse_embedding_segment_endpoints_separated :
  forall ls,
    sparse_embedding ls -> segment_endpoints_separated ls.
Proof.
  intros ls Hsparse l s r Heq.
  exact (proj2 (proj2 (Hsparse l s r Heq))).
Qed.

(* 矩形・延長線・端点についての局所的な分離条件から全域疎性を組み立てる。 *)
Lemma geometric_sparse_embedding :
  forall ls,
    (forall s, In s ls -> in_rect_or_endpoints [s] [s]) ->
    segment_rectangles_separated ls ->
    extensions_avoid_segment_rectangles ls ->
    segment_endpoints_separated ls ->
    sparse_embedding ls.
Proof.
  intros ls Hcontained Hrect Hext Hend l s r Heq.
  split.
  - intros p [Hhead | Hlast].
    + apply (Hext l s r Heq p). left. rewrite Heq. exact Hhead.
    + apply (Hext l s r Heq p). right. rewrite Heq. exact Hlast.
  - split.
    + intros t p Ht Hp. eapply Hrect; eauto.
    + eapply Hend. exact Heq.
Qed.

(* 全域疎性から、任意の非空な連続部分列の両端点での非交差を取り出す。 *)
Lemma sparse_embedding_sub_endpoints :
  forall l sub r,
    sub <> [] ->
    sparse_embedding (l ++ sub ++ r) ->
    sub_endpoints_do_not_cross l sub r.
Proof.
  intros l sub r Hsub Hsparse.
  destruct sub as [|first tail]; [contradiction|].
  assert (Hfirst : sub_endpoints_do_not_cross l [first] (tail ++ r)).
  { assert (Heq : l ++ first :: tail ++ r = l ++ [first] ++ (tail ++ r)).
    { reflexivity. }
    exact (proj2 (proj2 (Hsparse l first (tail ++ r) Heq))). }
  assert (Hne : first :: tail <> []) by discriminate.
  destruct (exists_last Hne) as [prefix [last Hdecomp]].
  assert (Hfull : l ++ first :: tail ++ r = (l ++ prefix) ++ [last] ++ r).
  { transitivity (l ++ (prefix ++ [last]) ++ r).
    - exact (f_equal (fun xs => l ++ xs ++ r) Hdecomp).
    - repeat rewrite app_assoc. reflexivity. }
  assert (Hlast : sub_endpoints_do_not_cross (l ++ prefix) [last] r).
  { exact (proj2 (proj2 (Hsparse (l ++ prefix) last r Hfull))). }
  assert (Hlastseg : last_segment (first :: tail) = last).
  { rewrite Hdecomp. unfold last_segment. apply last_last. }
  unfold sub_endpoints_do_not_cross in Hlast.
  rewrite <- Hfull in Hlast.
  unfold sub_endpoints_do_not_cross in Hfirst |- *.
  intros t1 t2 Hneq [Hinit | Hterm].
  - apply (Hfirst t1 t2 Hneq). now left.
  - apply (Hlast t1 t2 Hneq). right.
    now rewrite <- Hlastseg.
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

Lemma sparse_body_collision_impossible : forall ls tb to sb so,
  ls <> [] ->
  sparse_embedding ls ->
  nth_error ls (extend_index ls tb) = Some sb ->
  nth_error ls (extend_index ls to) = Some so ->
  extend_index ls tb <> extend_index ls to ->
  0 < extend_param ls tb <= 1 ->
  extend ls tb = point sb (extend_param ls tb) ->
  extend ls to = point so (extend_param ls to) ->
  extend ls tb = extend ls to ->
  (onHead_extend ls (extend ls to)
   \/ onSegment so (extend ls to)
   \/ onLast_extend ls (extend ls to)) ->
  False.
Proof.
  intros ls tb to sb so Hne Hsparse Hnthb Hntho Hindex Hbody
         Hreprb Hrepro Heq Hwhere.
  destruct (nth_error_other_context ls _ _ _ _ Hnthb Hntho Hindex)
    as [l [r [Hsplit Houtside]]].
  pose proof (Hsparse l sb r Hsplit) as [Hextension [Hrect Hendpoint]].
  assert (Honbody : onSegment sb (extend ls tb)).
  { exists (extend_param ls tb). split; [lra|]. now rewrite Hreprb. }
  destruct (segment_in_rect_or_endpoints sb (extend ls tb) Honbody)
    as [Hinit | [Hterm | Hinside]].
  - apply (Hendpoint tb to ltac:(congruence)).
    + left. now rewrite <- Hsplit.
    + now rewrite <- Hsplit.
  - apply (Hendpoint tb to ltac:(congruence)).
    + right. now rewrite <- Hsplit.
    + now rewrite <- Hsplit.
  - destruct Hwhere as [Hhead | [Honother | Hlast]].
    + apply (Hextension (extend ls tb)).
      * left. rewrite <- Hsplit. now rewrite Heq.
      * unfold in_rect, rect_of in Hinside. exact Hinside.
    + apply (Hrect so (extend ls tb) Houtside).
      * apply segment_in_rect_or_endpoints. now rewrite Heq.
      * unfold in_rect, rect_of in Hinside. exact Hinside.
    + apply (Hextension (extend ls tb)).
      * right. rewrite <- Hsplit. now rewrite Heq.
      * unfold in_rect, rect_of in Hinside. exact Hinside.
Qed.

Lemma sparse_extensions_open :
  forall ds ls,
    ls <> [] ->
    embed_listDir ds ls ->
    sparse_embedding ls ->
    extensions_disjoint ls ->
    ~ close ls.
Proof.
  intros ds ls Hne _ Hsparse Hdisjoint [t1 [t2 [Hneq Heq]]].
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
                Hne Hsparse Hnth1 Hnth2 Hi Hbody1 Hrepr1 Hrepr2 Heq).
      right; left.
      exists (extend_param ls t2). split; [lra|exact (eq_sym Hrepr2)].
  - destruct (Nat.eq_dec (extend_index ls t1) (extend_index ls t2)) as [Hi|Hi].
    + apply Hneq. exact (same_extend_piece_no_collision ls t1 t2 s1 s2 Hne Hnth1 Hnth2 Hi Hpoint).
    + eapply (sparse_body_collision_impossible ls t1 t2 s1 s2
                Hne Hsparse Hnth1 Hnth2 Hi Hbody1 Hrepr1 Hrepr2 Heq).
      left.
      destruct Hhead2 as [Hi2 Hp2].
      exact (extend_head_from_repr ls t2 s2 Hne Hnth2 Hrepr2 Hi2 Hp2).
  - destruct (Nat.eq_dec (extend_index ls t1) (extend_index ls t2)) as [Hi|Hi].
    + apply Hneq. exact (same_extend_piece_no_collision ls t1 t2 s1 s2 Hne Hnth1 Hnth2 Hi Hpoint).
    + eapply (sparse_body_collision_impossible ls t1 t2 s1 s2
                Hne Hsparse Hnth1 Hnth2 Hi Hbody1 Hrepr1 Hrepr2 Heq).
      right; right.
      destruct Hlast2 as [Hi2 Hp2].
      exact (extend_last_from_repr ls t2 s2 Hne Hnth2 Hrepr2 Hi2 Hp2).
  - destruct (Nat.eq_dec (extend_index ls t1) (extend_index ls t2)) as [Hi|Hi].
    + apply Hneq. exact (same_extend_piece_no_collision ls t1 t2 s1 s2 Hne Hnth1 Hnth2 Hi Hpoint).
    + eapply (sparse_body_collision_impossible ls t2 t1 s2 s1
                Hne Hsparse Hnth2 Hnth1 ltac:(congruence) Hbody2
                Hrepr2 Hrepr1 ltac:(congruence)).
      left. destruct Hhead1 as [Hi1 Hp1].
      exact (extend_head_from_repr ls t1 s1 Hne Hnth1 Hrepr1 Hi1 Hp1).
  - apply Hneq. eapply same_extend_piece_no_collision; eauto; lia.
  - apply (Hdisjoint (extend ls t1)).
    + destruct Hhead1 as [Hi1 Hp1].
      exact (extend_head_from_repr ls t1 s1 Hne Hnth1 Hrepr1 Hi1 Hp1).
    + rewrite Heq. destruct Hlast2 as [Hi2 Hp2].
      exact (extend_last_from_repr ls t2 s2 Hne Hnth2 Hrepr2 Hi2 Hp2).
  - destruct (Nat.eq_dec (extend_index ls t1) (extend_index ls t2)) as [Hi|Hi].
    + apply Hneq. exact (same_extend_piece_no_collision ls t1 t2 s1 s2 Hne Hnth1 Hnth2 Hi Hpoint).
    + eapply (sparse_body_collision_impossible ls t2 t1 s2 s1
                Hne Hsparse Hnth2 Hnth1 ltac:(congruence) Hbody2
                Hrepr2 Hrepr1 ltac:(congruence)).
      right; right. destruct Hlast1 as [Hi1 Hp1].
      exact (extend_last_from_repr ls t1 s1 Hne Hnth1 Hrepr1 Hi1 Hp1).
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

Lemma Region_eq_dec : forall g1 g2 : Region, {g1 = g2} + {g1 <> g2}.
Proof. decide equality. Qed.

Definition endpoint_of_seg (s : Segment) (p : Point) : Prop :=
  p = init s \/ p = term s.

Definition endpoint_of (ls : list Segment) (p : Point) : Prop :=
  exists s, In s ls /\ endpoint_of_seg s p.

(* 分類は曲線全体の配置を見て選ぶ。sub 上の端点は固定し、全体の先頭と
   末尾では延長線の傾きを平行移動で保てる配置を要求する。 *)
Parameter classify :
  list Segment -> list Segment -> list Segment -> Point -> Region.

Record ClassificationSpec (l sub r : list Segment) : Prop := {
  classified_sub_fixed :
    forall p, endpoint_of sub p -> classify l sub r p = RegFix;

  classified_head_same_region :
    l <> [] ->
    classify l sub r (init (hd_segment l)) =
      classify l sub r (term (hd_segment l))
    \/ (term (hd_segment l) = init (hd_segment sub)
        /\ fst (init (hd_segment sub)) < fst (init (hd_segment l)));

  classified_last_same_region :
    r <> [] ->
    classify l sub r (init (last_segment r)) =
      classify l sub r (term (last_segment r))
    \/ (init (last_segment r) = term (last_segment sub)
        /\ fst (term (last_segment r)) < fst (term (last_segment sub)))
}.

Axiom classify_spec :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    ClassificationSpec l sub r.

Definition shift (h : R) (g : Region) (p : Point) : Point :=
  match g with
  | RegFix  => p
  | RegUp   => (fst p, snd p + h)
  | RegDown => (fst p, snd p - h)
  end.

Definition operate_point
  (l sub r : list Segment) (h : R) (p : Point) : Point :=
  shift h (classify l sub r p) p.

Lemma shift_fst :
  forall h g p, fst (shift h g p) = fst p.
Proof. intros h g p. destruct g; reflexivity. Qed.

Lemma operate_point_fst :
  forall l sub r h p, fst (operate_point l sub r h p) = fst p.
Proof. intros. unfold operate_point. apply shift_fst. Qed.

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
           p Hend).
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

Definition all_reconnectable
  (l sub r : list Segment) (h : R) (ls : list Segment) : Prop :=
  forall s, In s ls -> reconnectable_after l sub r h s.

Definition reconnect_one
  (l sub r : list Segment) (h : R) (s : Segment) : Segment :=
  match excluded_middle_informative (reconnectable_after l sub r h s) with
  | left H => make_seg
      (operate_point l sub r h (init s))
      (operate_point l sub r h (term s))
      (orn_seg s) H
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
  - now apply make_seg_init.
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
  - now apply make_seg_term.
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
  - now apply make_seg_orn.
  - contradiction.
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
Admitted.

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

(* 固定した sub との接続点を含め、再接続後も全体が同じ向き列を埋め込む。 *)
Lemma reconnect_split_preserves_embed :
  forall l sub r h ds,
    sub <> [] ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    embed_listDir ds (reconnect_split l sub r h).
Admitted.

(* 疎な配置の各端点を同じ分類で動かすと、再接続後も全域疎性を保つ。 *)
Lemma reconnect_preserves_sparse :
  forall l sub r h,
    0 < h ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    sparse_embedding (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    sparse_embedding (reconnect_split l sub r h).
Admitted.

(* 先頭・末尾では同一領域の平行移動を選べるため、両延長線は交わらない。 *)
Lemma reconnect_preserves_extensions_disjoint :
  forall l sub r h,
    0 < h ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    sparse_embedding (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    extensions_disjoint (reconnect_split l sub r h).
Admitted.

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
    In s (l ++ r) ->
    forall p,
      in_segment_rect_or_endpoints (reconnect_one l sub r h s) p ->
      ~ in_rect (rect_of sub) p.
Admitted.

(* 一セグメント版の退避を、左右の再接続列全体へ持ち上げる。 *)
Lemma reconnect_sides_avoid_sub_rect :
  forall l sub r h s p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    In s (reconnect_segs l sub r h l ++ reconnect_segs l sub r h r) ->
    in_segment_rect_or_endpoints s p ->
    ~ in_rect (rect_of sub) p.
Proof.
  intros l sub r h s' p Hne Hconn Hmono Hh Hsparse Hrec Hs' Hp.
  rewrite in_app_iff in Hs'. destruct Hs' as [Hs' | Hs'];
    unfold reconnect_segs in Hs'; apply in_map_iff in Hs';
    destruct Hs' as [s [Heq Hs]]; subst s';
    eapply reconnect_one_avoids_sub_rect; eauto;
    rewrite in_app_iff; tauto.
Qed.

(* 延長線については、先頭・末尾の傾きを保つ分類条件から別途示す。 *)
Lemma reconnect_extensions_avoid_sub_rect :
  forall l sub r h p,
    connected (l ++ sub ++ r) ->
    well_split l sub r ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    (onHead_extend (reconnect_split l sub r h) p
     \/ onLast_extend (reconnect_split l sub r h) p) ->
    ~ in_rect (rect_of sub) p.
Admitted.

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
      ~ in_rect (rect_of sub) p.
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
    extensions_disjoint (l ++ sub ++ r) ->
    sparse_around
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
  assert (Hsparse' : sparse_embedding (reconnect_split l sub r h)).
  { apply reconnect_preserves_sparse; try assumption.
    exact (proj1 Hh). }
  split.
  - intros p Hextend.
    apply (reconnect_extensions_avoid_sub_rect
             l sub r h p Hconn Hws Hh Hsparse).
    exact Hextend.
  - split.
    + intros s p Hs Hp.
      exact (reconnect_sides_avoid_sub_rect
               l sub r h s p Hsubne HconnSub Hmono Hh
               Hsparse Hrec Hs Hp).
    + apply sparse_embedding_sub_endpoints.
      * exact Hsubne.
      * change (sparse_embedding (reconnect_split l sub r h)).
        exact Hsparse'.
Qed.

Lemma reconnect_preserves_open :
  forall ds l sub r h,
    0 < h ->
    sub <> [] ->
    x_monotone_segs sub ->
    all_reconnectable l sub r h (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    sparse_embedding (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    ~ close (reconnect_split l sub r h).
Proof.
  intros ds l sub r h Hh Hne Hmono Hrec Hembed Hsparse Hext.
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
  - apply reconnect_preserves_sparse; try assumption.
    exact (proj1 Hh).
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
  pose proof (proj1 Hh) as Hhpos.
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
      * exact Hhpos.
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
