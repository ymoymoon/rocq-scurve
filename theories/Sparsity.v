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
(*  1.  基本プリミティブ                                              *)
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

Lemma last_map_nonnil :
  forall (f : Segment -> Segment) ls,
    ls <> [] -> last_segment (map f ls) = f (last_segment ls).
Proof.
  intros f [|a tl] H; [contradiction|].
  clear H. unfold last_segment. revert a.
  induction tl as [|b tl IH]; intros a; simpl; [reflexivity|].
  exact (IH b).
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
(*  2.  長方形と sparse                                               *)
(* ================================================================= *)

Lemma Rmin_opp : forall a b, Rmin (- a) (- b) = - Rmax a b.
Proof. intros. unfold Rmin, Rmax. destruct (Rle_dec (-a) (-b)), (Rle_dec a b); lra. Qed.

Lemma Rmax_opp : forall a b, Rmax (- a) (- b) = - Rmin a b.
Proof. intros. unfold Rmin, Rmax. destruct (Rle_dec (-a) (-b)), (Rle_dec a b); lra. Qed.

(* 部分列の始点と終点を対角線にもつ長方形。
   1セグメントの長方形には rect_of [s] を用いる。 *)
Definition rect_of (sub : list Segment) : Rect :=
  let q0 := init (hd_segment sub) in
  let q3 := term (last_segment sub) in
  mkRect (Rmin (fst q0) (fst q3)) (Rmin (snd q0) (snd q3))
         (Rmax (fst q0) (fst q3)) (Rmax (snd q0) (snd q3)).

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

(* 先頭延長線と末尾延長線が互いに交わらない。 *)
Definition extensions_disjoint (ls : list Segment) : Prop :=
  forall p,
    onHead_extend ls p ->
    onLast_extend ls p ->
    False.

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

Definition segment_coord_min (coord : Point -> R) (s : Segment) : R :=
  Rmin (coord (init s)) (coord (term s)).

Definition segment_coord_max (coord : Point -> R) (s : Segment) : R :=
  Rmax (coord (init s)) (coord (term s)).

(* 非空なセグメント列の全端点における座標の最小値・最大値。 *)
Fixpoint segments_coord_min
  (coord : Point -> R) (s : Segment) (rest : list Segment) : R :=
  match rest with
  | [] => segment_coord_min coord s
  | t :: rest' =>
      Rmin (segment_coord_min coord s) (segments_coord_min coord t rest')
  end.

Fixpoint segments_coord_max
  (coord : Point -> R) (s : Segment) (rest : list Segment) : R :=
  match rest with
  | [] => segment_coord_max coord s
  | t :: rest' =>
      Rmax (segment_coord_max coord s) (segments_coord_max coord t rest')
  end.

(* 空列の bbox は退化した原点とする。非空列では全端点の厳密な bbox。 *)
Definition bbox_of (ls : list Segment) : Rect :=
  match ls with
  | [] => mkRect 0 0 0 0
  | first :: rest =>
      mkRect
        (segments_coord_min (fun p : Point => fst p) first rest)
        (segments_coord_min (fun p : Point => snd p) first rest)
        (segments_coord_max (fun p : Point => fst p) first rest)
        (segments_coord_max (fun p : Point => snd p) first rest)
  end.

Lemma segments_coord_bounds : forall coord s rest t,
  In t (s :: rest) ->
  segments_coord_min coord s rest <= segment_coord_min coord t
  /\ segment_coord_max coord t <= segments_coord_max coord s rest.
Proof.
  intros coord s rest. revert s.
  induction rest as [|a rest IH]; intros s t Hin.
  - simpl in Hin. destruct Hin as [<- | []]. split; reflexivity.
  - simpl in Hin |- *.
    destruct Hin as [<- | Hin].
    + split; [apply Rmin_l | apply Rmax_l].
    + destruct (IH a t Hin) as [Hmin Hmax].
      split.
      * eapply Rle_trans; [apply Rmin_r | exact Hmin].
      * eapply Rle_trans; [exact Hmax | apply Rmax_r].
Qed.

Lemma onSegment_y_bounds : forall s p,
  onSegment s p ->
  segment_coord_min (fun q : Point => snd q) s <= snd p
  /\ snd p <= segment_coord_max (fun q : Point => snd q) s.
Proof.
  intros s p Hp.
  destruct (segment_in_rectangle_or_endpoints s p Hp)
    as [-> | [-> | Hinside]].
  - split; [apply Rmin_l | apply Rmax_l].
  - split; [apply Rmin_r | apply Rmax_r].
  - unfold segment_coord_min, segment_coord_max.
    unfold in_open_segment_rectangle, in_rect, rect_between in Hinside.
    simpl in Hinside. lra.
Qed.

Lemma bbox_of_bounds :
  forall sub p, onSegmentlist sub p ->
    ry0 (bbox_of sub) <= snd p <= ry1 (bbox_of sub).
Proof.
  intros sub p [t [Ht Hp]].
  destruct sub as [|s rest]; [contradiction|].
  change
    (segments_coord_min (fun q : Point => snd q) s rest <= snd p
     <= segments_coord_max (fun q : Point => snd q) s rest).
  destruct (segments_coord_bounds (fun q : Point => snd q) s rest t Ht)
    as [Hmin Hmax].
  destruct (onSegment_y_bounds t p Hp) as [Hlo Hhi].
  split; lra.
Qed.

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
