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

(* Minus 側 (下向きに進む一方向曲線) の埋め込みで rightabove の代わりに使う，
    x 軸に関する鏡映版：終点が始点の右下側にある *)
Definition rightbelow (rr1 rr2 : Point) :=
  let (x1, y1) := rr1 in
  let (x2, y2) := rr2 in x1 < x2 /\ y2 < y1.

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


(* リスト補助（hd / last と map の交換。空リスト回避のため非空を仮定）*)
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


(* ---- 分解と存在 --------------------- *)
Lemma embed_split :
  forall ds1 sub_ds ds2 ls,
    embed_listDir (ds1 ++ sub_ds ++ ds2) ls ->
    exists l sub r,
      ls = l ++ sub ++ r
      /\ embed_listDir ds1 l /\ embed_listDir sub_ds sub /\ embed_listDir ds2 r.
Admitted.

(* 向き列の長さとセグメント列の長さは一致する（scurve レベル）*)
Lemma embed_nonnil :
  forall ds ls, embed_listDir ds ls -> ds <> [] -> ls <> [].
Admitted.

(* 単方向な向き列は空でない（is_one_way_scurve の定義から）*)
Lemma one_way_listDir_nonnil :
  forall ds, is_one_way_listDir ds -> ds <> [].
Admitted.


(* ================================================================= *)
(*  1．回転（90°×4）—                                                   *)
(*      8方向はどれも 90°の4回転のどれかで x 正成分を持つ向きに入る。    *)
(* ================================================================= *)

Inductive Rot : Type := R0 | R90 | R180 | R270.

Definition rot_pt (g : Rot) (p : Point) : Point :=
  match g with
  | R0   => p
  | R90  => (- snd p, fst p)
  | R180 => (- fst p, - snd p)
  | R270 => (snd p, - fst p)
  end.

Definition rot_inv (g : Rot) : Rot :=
  match g with R0 => R0 | R90 => R270 | R180 => R180 | R270 => R90 end.

Lemma rot_pt_inv : forall g p, rot_pt (rot_inv g) (rot_pt g p) = p.
Proof.
  intros g [x y]; destruct g; simpl;
    f_equal; try ring.
Qed.

(* セグメントの回転。point との整合を公理に置くと                *)
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

(* --- embed / close / sparse の回転不変性（★分離した補題）--- *)
Lemma rot_embed :
  forall g ds ls, embed_listDir ds ls -> embed_listDir ds (rot_segs g ls).
Admitted. 

Lemma rot_close :
  forall g ls, close (rot_segs g ls) -> close ls.
Admitted.  (* rot_pt が単射なので、交点は交点に対応 *)

Lemma rot_open :
  forall g ls, ~ close ls -> ~ close (rot_segs g ls).
Proof. intros g ls H Hc. apply H. eapply rot_close; exact Hc. Qed.

(* --- ★本命：単方向なら回転で x 正方向単調にできる --- *)
Lemma one_way_rot_exists :
  forall sub, is_one_way_embedding sub ->
    exists g : Rot, x_monotone_segs (rot_segs g sub).
Admitted.
(* 証明方針：is_one_way_scurve から、sub の全セグメントの向きは        *)
(*   「ある成分の符号が一定」な向きの集合に入る。8方向 d に対し、        *)
(*   g だけ回転させて {E, NE, SE}（= x 正成分）に入る g が存在：         *)
(*     E,NE,SE → R0 ／ N,NW → R270 ／ W,SW → R180 ／ S → R90          *)
(*   あとは rot_seg_point から init_x < term_x を計算するだけ。        *)

    
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


(* --- 長方形の輸送（★sparse の回転不変性の核）--- *)
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
(*  3.  境界線と移動                *)
(* ================================================================= *)

Definition Border := R -> R. (* これは良い？確かに境界線ならば関数だが，関数ならば境界線ではないので
   Border に関する変な補題などがなければ良い *)
Definition on_border (b : Border) (p : Point) : Prop := snd p = b (fst p).

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


(* 曲線全体と簡約対象 sub から境界線を1つ決める *)
Parameter make_border : list Segment -> list Segment -> Border.

(* 3分割された形での省略記法 *)
Definition border_of (l sub r : list Segment) : Border :=
  make_border (l ++ sub ++ r) sub.

(* 基本はセグメント全体を一定量だけ上下させる。                        *)
(* 境界線に接するセグメントは、自分の可変域の中だけで形を変える。       *)
Parameter operate_seg : list Segment -> list Segment -> R -> Segment -> Segment.

Definition operate_segs (ctx sub : list Segment) (h : R) (ls : list Segment)
  : list Segment := map (operate_seg ctx sub h) ls.

(* 可変域：曲線 ctx の中でセグメント s が形を変えてよい領域 *)
Definition Zone := Point -> Prop.
Parameter dzone : list Segment -> list Segment -> Segment -> Zone.

(* 曲線 P が境界線より上／下（以上／以下） *)
Definition weakly_above (b : Border) (P : Point -> Prop) : Prop :=
  forall p, P p -> b (fst p) <= snd p.
Definition weakly_below (b : Border) (P : Point -> Prop) : Prop :=
  forall p, P p -> snd p <= b (fst p).

(* --- operate_seg の仕様（境界線は make_border ctx sub で固定）--- *)

(* 仕様1：境界線上に完全に乗るセグメントは不動（簡約部分） *)
Axiom operate_seg_fix :
  forall ctx sub h s,
    (forall p, onSegment s p -> on_border (make_border ctx sub) p) ->
    operate_seg ctx sub h s = s.

(* 仕様2：向き（凸性を含む）の保存 *)
Axiom operate_seg_orn :
  forall ctx sub h s, orn_seg (operate_seg ctx sub h s) = orn_seg s.

(* 仕様3：移動後の点は「厳密な上下移動の像」か「自分の可変域の中」 *)
Axiom operate_seg_zone :
  forall ctx sub h s p, In s ctx ->
    onSegment (operate_seg ctx sub h s) p ->
      (exists p0, onSegment s p0
                  /\ p = operate_point (make_border ctx sub) h p0)
      \/ dzone ctx sub s p.

Axiom operate_seg_zone_head :
  forall ctx sub h s p, In s ctx ->
    onHead (operate_seg ctx sub h s) p ->
      (exists p0, onHead s p0
                  /\ p = operate_point (make_border ctx sub) h p0)
      \/ dzone ctx sub s p.

Axiom operate_seg_zone_last :
  forall ctx sub h s p, In s ctx ->
    onLast (operate_seg ctx sub h s) p ->
      (exists p0, onLast s p0
                  /\ p = operate_point (make_border ctx sub) h p0)
      \/ dzone ctx sub s p.

Lemma operate_segs_app :
  forall ctx sub h ls1 ls2,
    operate_segs ctx sub h (ls1 ++ ls2)
    = operate_segs ctx sub h ls1 ++ operate_segs ctx sub h ls2.
Proof. intros. unfold operate_segs. apply map_app. Qed.


  (* ================================================================= *)
(*  4.  make_border の性質                                            *)
(* ================================================================= *)

  (* --- 境界線との接触点の x 座標 --- *)
Definition contact_x (b : Border) (P : Point -> Prop) (x : R) : Prop :=
  exists p, P p /\ on_border b p /\ fst p = x.

(* sub を完全に覆う長方形（sub のみに依存）*)
(* y軸方向への移動はこの長方形の高さ以上必要 *)
Parameter bbox_of : list Segment -> Rect.
Axiom bbox_of_bounds :
  forall sub p, onSegmentlist sub p ->
    ry0 (bbox_of sub) <= snd p <= ry1 (bbox_of sub).

Definition outside_rect_x (sub : list Segment) (x : R) : Prop :=
  x < rx0 (rect_of sub) \/ rx1 (rect_of sub) < x.

(* 境界線を作れる前提（これ以外の仮定は使わない）*)
Definition well_split (l sub r : list Segment) : Prop :=
  sub <> [] /\ x_monotone_segs sub /\ ~ close (l ++ sub ++ r).

(* h の条件（sub のみに依存。境界線に依存しない）*)
Definition h_large (h : R) (sub : list Segment) : Prop :=
  0 < h /\ rect_height (bbox_of sub) < h.

Lemma choose_h : forall sub, exists h, h_large h sub.
Proof.
  intros sub. exists (Rmax 1 (rect_height (bbox_of sub) + 1)).
  unfold h_large. split.
  - eapply Rlt_le_trans; [apply Rlt_0_1 | apply Rmax_l].
  - eapply Rlt_le_trans; [| apply Rmax_r]. lra.
Qed.

(* ---- (A-1) sub は境界線のグラフの一部 ⇒ 不動 -------------------- *)
Lemma mb_fits :
  forall l sub r, well_split l sub r ->
    forall p, onSegmentlist sub p -> on_border (border_of l sub r) p.
Admitted.

(* ---- (A-2) 長方形の x 範囲では、境界線は sub のグラフそのもの ----- *)
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

(* ---- (Z-1) 可変域は長方形の内部と交わらない --- *)
Lemma mb_dz_rect :
  forall l sub r, well_split l sub r ->
    forall s p, In s (l ++ sub ++ r) ->
      dzone (l ++ sub ++ r) sub s p -> ~ in_rect (rect_of sub) p.
Admitted.

(* ---- (Z-2) 可変域には自分と隣接セグメント以外は入らない ---------- *)
(*      「端点近くで隣のセグメントが入り込む」問題への対応            *)
Parameter adjacent : list Segment -> Segment -> Segment -> Prop.

Lemma mb_dz_local :
  forall l sub r, well_split l sub r ->
    forall s s' p, In s (l ++ sub ++ r) -> In s' (l ++ sub ++ r) ->
      dzone (l ++ sub ++ r) sub s p -> onSegment s' p ->
      s = s' \/ adjacent (l ++ sub ++ r) s s'.
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
(*  5.  移動先が長方形に入らないこと                                   *)
(* ================================================================= *)

Lemma operate_pt_not_in_rect :
  forall l sub r h (P : Point -> Prop) p0,
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

  - (* RegFix : 不動。境界線に触るので接触点 ⇒ x 範囲の外 ⇒ 矛盾 *)
    destruct Hin as [[Hx0 Hx1] _].
    assert (Hc : contact_x (border_of l sub r) P (fst p0)).
    { exists p0. repeat split;
      [exact HP | apply (classify_RegFix_char _ p0 Hg)]. }
    destruct (Hct _ Hc); unfold outside_rect_x in *; lra.

  - (* RegUp : 上へ h。b(x) は bbox の中 ＆ h > bbox の高さ ⇒ 矛盾 *)
    pose proof (classify_RegUp_char _ p0 Hg) as Hup.
    destruct Hin as [[Hx0 Hx1] [Hy0 Hy1]]. cbn [fst snd] in *.
    destruct (mb_cover l sub r Hws (fst p0)) as [q [Hq [Hqx Hqy]]]; [lra|].
    pose proof (bbox_of_bounds sub q Hq) as [Hql Hqr].
    (* rewrite Hqx in Hqy. lra. *)
    admit.

  - (* RegDown : 下へ h。対称 *)
    pose proof (classify_RegDown_char _ p0 Hg) as Hdn.
    destruct Hin as [[Hx0 Hx1] [Hy0 Hy1]]. cbn [fst snd] in *.
    destruct (mb_cover l sub r Hws (fst p0)) as [q [Hq [Hqx Hqy]]]; [lra|].
    pose proof (bbox_of_bounds sub q Hq) as [Hql Hqr].
    (* rewrite Hqx in Hqy. lra. *)
    admit.
Admitted.


(* ================================================================= *)
(*  6.  operate の構造補題                                            *)
(* ================================================================= *)

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


(* ---- Lemma C : 接続の丸め（★独立の難所）------------------------- *)
(* 境界線と交わるセグメントは、可変域の中だけで形を変えて向きを保つ    *)
Lemma reconnect_one_segment :
  forall ctx sub h s,
    ~ weakly_above (make_border ctx sub) (onSegment s) ->
    ~ weakly_below (make_border ctx sub) (onSegment s) ->
    orn_seg (operate_seg ctx sub h s) = orn_seg s.
Admitted.

(* ---- Lemma D : 埋め込みの保存 ----------------------------------- *)
Lemma operate_preserves_embed :
  forall ctx sub h ds ls,
    embed_listDir ds ls -> embed_listDir ds (operate_segs ctx sub h ls).
Admitted.

(* ---- Lemma E : 開の保存 ----------------------------------------- *)
(*  [1] セグメント×セグメント：同領域なら同じ h 平行移動 ⇒ 移動前も    *)
(*      交差して矛盾／可変域に入る場合は mb_dz_local より隣接 ⇒       *)
(*      共有端点であって自己交差ではない                              *)
(*  [2] セグメント×延長線、[3] 延長線×延長線：同様に帰着              *)
Lemma operate_preserves_open :
  forall l sub r h, well_split l sub r ->
    ~ close (operate_segs (l ++ sub ++ r) sub h l
             ++ sub
             ++ operate_segs (l ++ sub ++ r) sub h r).
Admitted.

(* ---- Lemma F : 疎になる（3ケースすべて証明済み）------------------ *)
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
    assert (Hin : In (hd_segment (l ++ sub ++ r)) (l ++ sub ++ r)).
    { destruct l as [|a l']; simpl;
      [destruct sub as [|s sub']; [contradiction | left; reflexivity]
      | left; reflexivity]. }
    destruct (operate_seg_zone_head _ sub h _ p Hin Hhead)
      as [[p0 [Hp0 Heq]] | Hz].
    + subst p. eapply (operate_pt_not_in_rect l sub r h
                         (onHead_extend (l ++ sub ++ r))); eauto.
      apply (mb_ct_head l sub r Hws).
    + apply (mb_dz_rect l sub r Hws _ p Hin Hz).

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
    destruct (operate_seg_zone _ sub h s0 p Hinctx Hp)
      as [[p0 [Hp0 Heq]] | Hz].
    + subst p. eapply (operate_pt_not_in_rect l sub r h
                         (onSegmentlist (l ++ r))); eauto.
      * apply (mb_ct_seg l sub r Hws).
      * exists s0. split; assumption.
    + apply (mb_dz_rect l sub r Hws _ p Hinctx Hz).

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
    destruct (operate_seg_zone_last _ sub h _ p Hin Hlast)
      as [[p0 [Hp0 Heq]] | Hz].
    + subst p. eapply (operate_pt_not_in_rect l sub r h
                         (onLast_extend (l ++ sub ++ r))); eauto.
      apply (mb_ct_last l sub r Hws).
    + apply (mb_dz_rect l sub r Hws _ p Hin Hz).
Qed.



(* ================================================================= *)
(*  7.  最終命題（回転 → 核補題 → 逆回転）                            *)
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
   /\ sub' <> [].                       (* ★追加 *)
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
  - subst ctx. eapply operate_preserves_open; exact Hws.
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
