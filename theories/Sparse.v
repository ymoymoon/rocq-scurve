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

Definition hd_segment ls := hd default_segment ls.
Definition last_segment ls := last ls default_segment.

Parameter orn_seg   : Segment -> Direction.

Definition rightabove (rr1 rr2 : Point) :=
  let (x1, y1) := rr1 in
  let (x2, y2) := rr2 in x1 < x2 /\ y1 < y2.

(* x 単調 = x 軸正の向きに進み続ける（y は無関係） *)
Definition x_monotone_seg  (s : Segment) : Prop := init_x s < term_x s.
Definition x_monotone_segs (ls : list Segment) : Prop :=
  forall s, In s ls -> x_monotone_seg s.


(* TODO: 空リストを省く *)
Definition onHead (seg: Segment) (rr : Point) := exists (t:R), t <= 0 /\ point seg t = rr.
Definition onHead_extend (ls: list Segment) (rr : Point) := onHead (hd_segment ls) rr.
Definition onLast (seg: Segment) (rr : Point) := exists (t:R), 1 <= t /\ point seg t = rr.
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


(* ================================================================= *)
(*  1.  長方形と sparse                               *)
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


(* ================================================================= *)
(*  2.  境界線：x の関数                *)
(* ================================================================= *)

Definition Border := R -> R. (* これは良い？確かに境界線ならば関数だが，関数ならば境界線ではないので
   Border に関する変な補題などがなければ良い *)
Definition on_border (b : Border) (p : Point) : Prop := snd p = b (fst p).

Inductive Region : Type := RegFix | RegUp | RegDown.

(* sub を引数に取らない：境界線との上下比較だけで決まる *)
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


(* ================================================================= *)
(*  3.  operate（Segment 1 本 → Segment 1 本、eps は丸め幅）           *)
(* ================================================================= *)

(* 基本はセグメント全体を，一定の値だけ上下させる．
    境界線に端点を持つセグメントは，左右の微小領域の中で少し形を変え，境界線の端点を通るようにする *)
Parameter operate_seg : Border -> R -> R -> Segment -> Segment.

Definition operate_segs (b : Border) (eps h : R) (ls : list Segment)
  : list Segment := map (operate_seg b eps h) ls.

(* 曲線 P は境界線 b より上（以上）にある *)
Definition weakly_above (b : Border) (P : Point -> Prop) : Prop :=
  forall p, P p -> b (fst p) <= snd p.
Definition weakly_below (b : Border) (P : Point -> Prop) : Prop :=
  forall p, P p -> snd p <= b (fst p).

(* 仕様1：境界線上に完全に乗るセグメントは不動（簡約部分） *)
Axiom operate_seg_fix :
  forall b eps h s,
    (forall p, onSegment s p -> on_border b p) -> operate_seg b eps h s = s.

(* 仕様2：向き（凸性）の保存（単一領域なら鉛直平行移動、交差時は Lemma C） *)
Axiom operate_seg_orn :
  forall b eps h s, orn_seg (operate_seg b eps h s) = orn_seg s.

(* 仕様3：移動後の点は「厳密な平行移動」か「境界線との接触点から eps 以内の *)
(*        丸め部分」のいずれか（写真：境界線部分は不変なので調整）           *)
Axiom operate_seg_zone :
  forall b eps h s p,
    onSegment (operate_seg b eps h s) p ->
    exists p0, onSegment s p0 /\ 
      (p = operate_point b h p0
      \/ (on_border b p0 /\ Rabs (fst p - fst p0) <= eps)). (* TODO : ちょっと違う．また，ε をとった時，端点近くではすぐ横のセグメントが入り込んでしまうので対応必要 *)

Lemma operate_segs_app :
  forall b eps h ls1 ls2,
    operate_segs b eps h (ls1 ++ ls2)
    = operate_segs b eps h ls1 ++ operate_segs b eps h ls2.
Proof. intros. unfold operate_segs. apply map_app. Qed.

Lemma map_id_pointwise :
  forall (f : Segment -> Segment) (ls : list Segment),
    (forall s, In s ls -> f s = s) -> map f ls = ls.
Proof.
  induction ls as [|a tl IH]; intros H; simpl; [reflexivity|].
  rewrite H by (left; reflexivity).
  rewrite IH by (intros s Hs; apply H; right; exact Hs). reflexivity.
Qed.


(* ================================================================= *)
(*  4.  良い境界線の仕様                                                *)
(* ================================================================= *)

(* --- 境界線との接触点の x 座標 --- *)
Definition contact_x (b : Border) (P : Point -> Prop) (x : R) : Prop :=
  exists p, P p /\ on_border b p /\ fst p = x.

(* --- sub の鉛直方向のはみ出し幅（x単調でも y単調ではないので必要）--- *)
(* TODO : はみだしていても移動に支障ないので不要 *)
Parameter vspan : list Segment -> R.
Axiom vspan_nonneg : forall sub, 0 <= vspan sub.
Axiom vspan_bounds :
  forall sub p, onSegmentlist sub p ->
    ry0 (rect_of sub) - vspan sub <= snd p <= ry1 (rect_of sub) + vspan sub.

(* TODO : 中身の仕様は Lemma でわけたいが．． *)
Record good_border (b : Border) (l sub r : list Segment) : Prop := {
  (* (A-1) sub は境界線のグラフの一部 ⇒ 不動 *)
  gb_fits : forall p, onSegmentlist sub p -> on_border b p;

  (* (A-2) 長方形の x 範囲では、境界線は sub のグラフそのもの *)
  gb_cover : forall x, rx0 (rect_of sub) <= x <= rx1 (rect_of sub) ->
               exists q, onSegmentlist sub q /\ fst q = x /\ snd q = b x;

  (* (A-3) l, r の各セグメントは境界線を横断しない *)
  gb_side : forall s, In s (l ++ r) ->
              weakly_above b (onSegment s) \/ weakly_below b (onSegment s);

  (* (A-4) 延長線（半直線）も横断しない *)
  gb_side_head : weakly_above b (onHead_extend (l ++ sub ++ r))
              \/ weakly_below b (onHead_extend (l ++ sub ++ r));
  gb_side_last : weakly_above b (onLast_extend (l ++ sub ++ r))
              \/ weakly_below b (onLast_extend (l ++ sub ++ r));

  (* (A-5) l, r と延長線が境界線に触る x は、長方形の x 範囲の外 *)
  gb_ct_seg : forall x, contact_x b (onSegmentlist (l ++ r)) x ->
                x < rx0 (rect_of sub) \/ rx1 (rect_of sub) < x;
  gb_ct_head : forall x, contact_x b (onHead_extend (l ++ sub ++ r)) x ->
                x < rx0 (rect_of sub) \/ rx1 (rect_of sub) < x;
  gb_ct_last : forall x, contact_x b (onLast_extend (l ++ sub ++ r)) x ->
                x < rx0 (rect_of sub) \/ rx1 (rect_of sub) < x
}.

(* ε は「接触 x が長方形の x 範囲から ε 以上離れている」ように取る *)
(* TODO : 下と併せて eps は明示せず，各セグメントは自分の周りに，他の曲線が入ってこない領域を持ち，
    その中で形を変えて，などできる，とするほうが？ *)
Definition eps_separates (b : Border) (eps : R) (l sub r : list Segment) : Prop :=
    (forall x, contact_x b (onSegmentlist (l ++ r)) x ->
       x < rx0 (rect_of sub) - eps \/ rx1 (rect_of sub) + eps < x)
 /\ (forall x, contact_x b (onHead_extend (l ++ sub ++ r)) x ->
       x < rx0 (rect_of sub) - eps \/ rx1 (rect_of sub) + eps < x)
 /\ (forall x, contact_x b (onLast_extend (l ++ sub ++ r)) x ->
       x < rx0 (rect_of sub) - eps \/ rx1 (rect_of sub) + eps < x).
       
(* ε とった時，端点近くではすぐ横のセグメントが入り込んでしまうので対応必要 *)
Axiom operate_seg_zone_head :
  forall b eps h s p,
    onHead (operate_seg b eps h s) p ->
      (exists p0, onHead s p0 /\ p = shift h (classify b p0) p0)
   \/ (exists p0, onHead s p0 /\ on_border b p0
                  /\ Rabs (fst p - fst p0) <= eps).

Axiom operate_seg_zone_last :
  forall b eps h s p,
    onLast (operate_seg b eps h s) p ->
      (exists p0, onLast s p0 /\ p = shift h (classify b p0) p0)
   \/ (exists p0, onLast s p0 /\ on_border b p0
                  /\ Rabs (fst p - fst p0) <= eps).


Lemma zone_not_in_rect :
  forall b eps h sub (P : Point -> Prop) p p0,
    0 < eps ->
    rect_height (rect_of sub) + vspan sub < h ->
    (forall x, rx0 (rect_of sub) <= x <= rx1 (rect_of sub) ->
       exists q, onSegmentlist sub q /\ fst q = x /\ snd q = b x) ->
    (forall x, contact_x b P x ->
       x < rx0 (rect_of sub) - eps \/ rx1 (rect_of sub) + eps < x) ->
    P p0 ->
    ( p = shift h (classify b p0) p0
      \/ (on_border b p0 /\ Rabs (fst p - fst p0) <= eps) ) ->
    ~ in_rect (rect_of sub) p.
Proof.
  intros b eps h sub P p p0 Heps Hh Hcover Hct HP Hzone Hin.
  pose proof (vspan_nonneg sub) as Hv.
  unfold in_rect in Hin. destruct Hin as [[Hx0 Hx1] [Hy0 Hy1]].
  unfold rect_height in Hh.
  destruct Hzone as [Hshift | [Hb Hd]].

  - (* ---- 厳密な平行移動の場合 ---- *)
    destruct (classify b p0) eqn:Hg;
      unfold shift in Hshift.

    + (* RegFix : 不動。境界線に触っているので接触点、よって x 範囲の外 *)
      subst p.
      assert (Hc : contact_x b P (fst p0)). {
        exists p0; repeat split;
        [exact HP | apply (classify_RegFix_char b p0 Hg) ].
      }
      destruct (Hct _ Hc); lra.

    + (* RegUp : 上へ h。p が長方形内 ⇒ 元の点は長方形より h 下 ⇒ 境界線も下 *)
      pose proof (classify_RegUp_char b p0 Hg) as Hup.
      subst p. cbn [fst snd] in Hx0, Hx1, Hy0, Hy1.
      destruct (Hcover (fst p0)) as [q [Hq [Hqx Hqy]]]; [lra|].
      pose proof (vspan_bounds sub q Hq) as [Hql Hqr].
      lra.

    + (* RegDown : 下へ h。対称な議論 *)
      pose proof (classify_RegDown_char b p0 Hg) as Hdn.
      subst p. cbn [fst snd] in Hx0, Hx1, Hy0, Hy1.
      destruct (Hcover (fst p0)) as [q [Hq [Hqx Hqy]]]; [lra|].
      pose proof (vspan_bounds sub q Hq) as [Hql Hqr].
      lra.

  - (* ---- 丸め（写真：境界線と交わる所は境界線部分が不変なので調整）---- *)
    (* 丸めは接触点から x 方向 eps 以内。接触点は x 範囲から eps 以上外 *)
    assert (Hd' : fst p - fst p0 <= eps /\ - eps <= fst p - fst p0).
    { unfold Rabs in Hd. destruct (Rcase_abs (fst p - fst p0)); lra. }
    destruct Hd' as [Hd1 Hd2].
    assert (Hc : contact_x b P (fst p0))
      by (exists p0; repeat split; [exact HP | exact Hb]).
    destruct (Hct _ Hc); lra.
Qed.


(* ---- 分解と存在（既出）---------------------------------------- *)
Lemma embed_split :
  forall ds1 sub_ds ds2 ls,
    embed_listDir (ds1 ++ sub_ds ++ ds2) ls ->
    exists l sub r,
      ls = l ++ sub ++ r
      /\ embed_listDir ds1 l /\ embed_listDir sub_ds sub /\ embed_listDir ds2 r.
Admitted.

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

(* x 単調にできる *)
Lemma one_way_gives_xmonotone :
  forall ds l sub_ls r,
    embed_listDir ds (l ++ sub_ls ++ r) ->
    is_one_way_embedding sub_ls ->
    ~ close (l ++ sub_ls ++ r) -> (* TODO : この補題とは分離すべき *)
    exists l' sub_ls' r',
    embed_listDir ds (l' ++ sub_ls' ++ r') /\
    x_monotone_segs sub_ls'/\
    ~ close (l' ++ sub_ls' ++ r').
Proof.
  (* x 単調でなければ90度回転させる *)
Admitted.

(* ---- Lemma A : 良い境界線の存在（停止性が核）-------- *)
Lemma border_good :
  forall l sub r,
    x_monotone_segs sub -> ~ close (l ++ sub ++ r) ->
    exists b, good_border b l sub r.
Admitted.

(* ---- ε の選択（有限個のコンパクト集合と閉区間の正距離）----------- *)
(* TODO : いくらか上で書いた変更 *)
Lemma choose_eps :
  forall b l sub r, good_border b l sub r ->
    exists eps, 0 < eps /\ eps_separates b eps l sub r.
Admitted.

(* ---- h の選択（sub のみに依存。境界線に依存しない）---------------- *)
Lemma choose_h :
  forall sub, exists h,
    0 < h /\ rect_width (rect_of sub) < h
          /\ rect_height (rect_of sub) + vspan sub < h.
Admitted.

(* ---- Lemma C : 接続の丸め（★独立の難所）------------------------ *)
(* 境界線と交わるセグメントは、境界線上の部分が不変なので、向きを    *)
(* 保ったまま「同じ向きのセグメント1本」に調整できる                  *)
(* ついでに傾きも同じに *)
Lemma reconnect_one_segment :
  forall b eps h s,
    ~ weakly_above b (onSegment s) -> ~ weakly_below b (onSegment s) ->
    orn_seg (operate_seg b eps h s) = orn_seg s.
Admitted.

(* ---- sub は不動、リストは3分割を保つ（証明済み）----------------- *)
Lemma operate_segs_fix :
  forall b eps h l sub r, good_border b l sub r ->
    operate_segs b eps h sub = sub.
Proof.
  intros b eps h l sub r Hgb. unfold operate_segs.
  apply map_id_pointwise. intros s Hs.
  apply operate_seg_fix. intros p Hp.
  apply (gb_fits _ _ _ _ Hgb). exists s. split; assumption.
Qed.

Lemma operate_split :
  forall b eps h l sub r, good_border b l sub r ->
    operate_segs b eps h (l ++ sub ++ r)
    = operate_segs b eps h l ++ sub ++ operate_segs b eps h r.
Proof.
  intros b eps h l sub r Hgb.
  rewrite !operate_segs_app.
  rewrite (operate_segs_fix b eps h l sub r Hgb). reflexivity.
Qed.

(* ---- Lemma D : 埋め込みの保存 ---------------------------------- *)
(* 単一領域では鉛直平行移動（operate_seg_zone の第1枝）、境界線と交わる  *)
(* 場合は Lemma C。いずれも orn/cvx 不変（operate_seg_orn/cvx）。      *)
Lemma operate_preserves_embed :
  forall b eps h ds ls,
    embed_listDir ds ls -> embed_listDir ds (operate_segs b eps h ls).
Admitted.

(* ---- Lemma E : 開の保存 -------------- *)
(* セグメントは有限・延長線は半直線なので「値が∞」の場合分けは不要。   *)
(*  [1] セグメント×セグメント：同じ領域なら同じ h 平行移動 ⇒ 移動前も *)
(*      交差して矛盾／境界線と交わる側は eps 近傍の議論で矛盾            *)
(*  [2] セグメント×延長線、[3] 延長線×延長線：同様に帰着              *)
Lemma operate_preserves_open :
  forall b eps h l sub r,
    0 < eps -> good_border b l sub r -> eps_separates b eps l sub r ->
    ~ close (l ++ sub ++ r) ->
    ~ close (operate_segs b eps h l ++ sub ++ operate_segs b eps h r).
Admitted.

(* ---- Lemma F : 疎になる ----------------- *)
Lemma operate_gives_sparse :
  forall b eps h l sub r,
    0 < eps -> good_border b l sub r -> eps_separates b eps l sub r ->
    rect_height (rect_of sub) + vspan sub < h ->
    sparse (operate_segs b eps h l) sub (operate_segs b eps h r).
Proof.
  intros b eps h l sub r Heps Hgb Hsep Hh.
  destruct Hsep as [HsepS [HsepH HsepL]].
  unfold sparse. intros p H. destruct H as [Hhead |[ Hmid | Hlast]].

  - (* [head] 先頭の延長線が長方形に入らない *)
    (* operate 後の先頭セグメントは operate_seg b eps h (hd_segment (l++sub++r)) *)
    (* operate_seg_zone_head + zone_not_in_rect（P := onHead_extend ...）で同型 *)
    admit.

  - (* [mid] l, r のセグメントが長方形に入らない *)
    destruct Hmid as [s [Hs Hp]].
    (* s は operate_seg の像なので、元のセグメント s0 を取り出す *)
    apply in_app_or in Hs.
    assert (Hs0 : exists s0, In s0 (l ++ r) /\ s = operate_seg b eps h s0).
    { destruct Hs as [H|H]; unfold operate_segs in H;
      apply in_map_iff in H; destruct H as [s0 [Heq Hin]];
      exists s0; split; [apply in_or_app; auto | auto | apply in_or_app; auto | auto]. }
    destruct Hs0 as [s0 [Hin0 Heq0]]. subst s.
    destruct (operate_seg_zone b eps h s0 p Hp) as [p0 [Hp0 [Hsh | [Hb Hd]]]].
    + eapply (zone_not_in_rect b eps h sub (onSegmentlist (l ++ r)) p p0);
        eauto.
      * apply (gb_cover _ _ _ _ Hgb).
      * exists s0; split; assumption.
    + eapply (zone_not_in_rect b eps h sub (onSegmentlist (l ++ r)) p p0);
        eauto.
      * apply (gb_cover _ _ _ _ Hgb).
      * exists s0; split; assumption.

  - (* [last] 末尾の延長線も同様（operate_seg_zone_last を使う）*)
    admit.
Admitted.


(* ================================================================= *)
(*  7.  最終命題                                                      *)
(* ================================================================= *)

Lemma embed_sparsely_listDir (ds1 sub_ds ds2 : list Direction) :
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

  (* Step 1 : 許容可能性から開埋め込みを1つ得る *)
  destruct (admissible_gives_open_embed _ Hadm) as [ls0 [Hemb0 Hopen0]].

  (* Step 2 : 3 分割 *)
  destruct (embed_split _ _ _ _ Hemb0)
    as (l0 & sub0 & r0 & Heq & Hl0 & Hsub0 & Hr0).
  subst ls0.

  (* Step 3 : x 単調性 *)
  assert (Honeway : is_one_way_embedding sub0). {
    destruct Hsub0 as [sc [Hdir Hembed]].
    exists sc.
    split; auto.
    destruct Hone as [sc' [Hdir' Honeway]].
    apply (is_one_way_same_direction _ _ (eq_trans Hdir' (eq_sym Hdir)) Honeway).
  }
  destruct (one_way_gives_xmonotone _ _ _ _ Hemb0 Honeway Hopen0) as [l' [sub' [r' [Hembed [Hx Hopen']]]]].

  (* Step 4 : h を sub' だけから決める（★境界線に依存しない）*)
  destruct (choose_h sub') as [h [Hh [HhW HhH]]].

  (* Step 5 : 境界線を取る（Lemma A）*)
  destruct (border_good l' sub' r' Hx Hopen') as [b Hgb].

  (* Step 6 : ε を境界線の後で決める *)
  destruct (choose_eps b l' sub' r' Hgb) as [eps [Heps Hsep]].

  (* Step 7 : operate して結論 *)
  exists (operate_segs b eps h l'), (operate_segs b eps h r'), sub'.
  repeat split.
  - eapply operate_preserves_embed. admit.
  - admit. 
  - eapply operate_preserves_embed. admit.
  - rewrite <- (operate_split b eps h l' sub' r' Hgb).
    eapply operate_preserves_embed; eauto.
  - eapply operate_preserves_open; eauto.
  - eapply operate_gives_sparse; eauto.
Admitted.