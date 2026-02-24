Require Import Admissible.
Require Import Reduction.
Require Import Stdlib.Reals.Reals.
Require Import Embed.
Require Import PrimitiveSegment.
Require Import Segment.
Import ListNotations.


(* --------------------------------------------------------------------------- *)
(* 単なるリストに関する補題など *)

Lemma hd_app : forall {A : Type} (a b : list A) (dummy : A),
  a <> [] ->
  hd dummy a = hd dummy (a ++ b).
Proof.
  intros A a b dummy H.
  destruct a.
  - contradiction.
  - reflexivity.
Qed.

Lemma last_app : forall {A : Type} (l l' : list A) (d : A),
  l' <> [] ->
  last l' d = last (l ++ l') d.
Proof.
  intros A l.
  induction l as [| x l IH]; intros l' d Hneq.
  - (* l = [] *)
    simpl.
    reflexivity.
  - (* l = x :: l *)
    simpl.
		assert (H : l ++ l' <> []). {
			intros H1. apply app_eq_nil in H1. 
			destruct H1. contradiction.
		}
    apply (IH l' d) in Hneq.
    rewrite <- Hneq.
		destruct (l ++ l'); congruence.
Qed.

Lemma last_app_cons : forall {A} (l l' : list A) (x dummy : A),
	last (l ++ x :: l') dummy = last (x :: l') dummy.
Proof.
	intros A l l' x d.
  rewrite <- last_app; congruence.
Qed.

Lemma list_head_tail : forall {A} (dummy: A) (l: list A),
	l <> [] -> (hd dummy l) :: (tl l) = l.
Proof. 
	intros A dummy l H. 
	induction l.
	- contradiction.
	- reflexivity. 
Qed.

Lemma list_map_head : forall {A B} (dummy: A) (x: B) (l: list A) (l': list B) f,
	map f l = x :: l' -> f (hd dummy l) = x.
Proof. 
	intros A B dummy x l l' f H.
	induction l.
	- discriminate.
	- simpl in *. congruence. 
Qed.

Lemma app_split :
  forall (A : Type) (l1 l2 l1' l2' : list A),
  l1 ++ l2 = l1' ++ l2' ->
  (exists a l, l1' = l1 ++ a :: l /\ l2 = a :: l ++ l2')
	\/
	(l1' = l1 /\ l2 = l2')
  \/
  (exists a l, l1 = l1' ++ a :: l /\ a :: l ++ l2 = l2').
Proof.
  intros A l1 l2 l1' l2' Heq.
	apply app_eq_app in Heq.
	destruct Heq as [l [[H1 H2] | [H1 H2]]].
	- (* length l1 >= length l1' *)
		destruct l as [ | x l'].
		+ (* length l1 = length l1' *)
			right; left. 
			rewrite app_nil_r in H1. simpl in H2.
			split; auto.
		+ (* length l1 > length l1' *)
			right; right.
			exists x, l'.
			split; auto.
	- (* length l1 <= length l1' *)
		destruct l as [ | x l'].
		+ (* length l1 = length l1' *)
			right; left. 
			rewrite app_nil_r in H1. simpl in H2.
			split; auto.
		+ (* length l1 < length l1' *)
			left.
			exists x, l'.
			split; auto.
Qed.

(** a と b がこの順でリストに入っている *)
Definition In_order {A} (a b : A) (l : list A) : Prop :=
  exists l1 l2 l3, l = l1 ++ a :: l2 ++ b :: l3.

Lemma In_split_In_order : forall {A} (a b : A) l,
	In a l 
	-> In b l
	-> a = b \/ In_order a b l \/ In_order b a l.
Proof.
	intros A a b l Ha Hb.
	apply in_split in Ha.
	destruct Ha as [la1 [la2 Ha]].
	apply in_split in Hb.
	destruct Hb as [lb1 [lb2 H]].
	subst.
	apply app_split in H.
	destruct H as [[x [l' [_ H]]] | [[_ H] | [x [l' [H1 H2]]]]].
	- right; left.
		injection H. intros H1 _. subst.
		exists la1, l', lb2. reflexivity.
	- left. injection H. auto.
  - repeat right.
		injection H2. intros _ Hb. subst.
		exists lb1, l', la2. 
		rewrite <- app_assoc. f_equal.
Qed.

Lemma In_order_split : forall {A} (a b : A) l1 l2 l3,
	In_order a b (l1 ++ l2 ++ l3)
	-> In_order a b l2 (* a も b も l2 に入っている *)
		\/ (In a l2 /\ In b l3) (* a のみ l2 に入っている *)
		\/ (In a l1 /\ In b l2) (* b のみ l2 に入っている *)
		\/ In_order a b (l1 ++ l3). (* a も b も l2 に入っていない *)
Proof.
	intros A a b l1 l2 l3 H.
	destruct H as [l1' [l2' [l3' H]]].
	(* a, b が l2 に入っているかどうかで場合分け *)
	apply app_split in H.
	destruct H as [[x [l [_ Ha_right]]] | [H | [x [l [Ha_l1 H]]]]].
	- (* a が l2 ++ l3 に入っている場合１ *)
		rewrite app_comm_cons in Ha_right. 
		apply app_split in Ha_right.
		destruct Ha_right as [[x' [l' [_ Ha_l3]]] | [[_ Ha_l3] | [x' [l' [Ha_l2 H]]]]].
		+ (* a, b が l3 に入っている場合１ *)
			right; right; right.
			exists (l1 ++ x' :: l'), l2', l3'.
			rewrite Ha_l3. rewrite <- app_assoc.
			f_equal.
		+ (* a, b が l3 に入っている場合２ *)
			right; right; right.
			exists l1, l2', l3'.
			rewrite Ha_l3. 
			f_equal.
		+ (* a が l2 に入っている場合 *)
			injection H. intros H1 Ha. subst.
			apply app_split in H1.
			destruct H1 as [[x'' [l'' [_ Hb_l3]]] | [[_ Hb_l3] | [x'' [l'' [Hb_l2 H1]]]]].
			* (* b が l3 に入っている場合１ *)
				right; left. subst. split; try apply in_elt; try apply in_cons.
				apply in_elt.
			* (* b が l3 に入っている場合２ *)
				right; left. subst. split; try apply in_elt; apply in_eq.
			* (* b が l2 に入っている場合 *)
				left. injection H1. intros _ Hb. subst.
				exists (x::l), l2', l''. reflexivity.
	- (* a が l2 ++ l3 に入っている場合２ *)
		destruct l2 as [ | x l]. 
		+ (* a, b が l3 に入っている場合 *)
			right; right; right.
			destruct H as [H1 H2]. rewrite app_nil_l in H2.
			subst.
			exists l1, l2', l3'. reflexivity.
		+ (* a が l2 に入っている場合 *)
			destruct H as [H1 H2].
			injection H2. intros H3 Ha. subst.
			apply app_split in H3.
			destruct H3 as [[x'' [l'' [_ Hb_l3]]] | [[_ Hb_l3] | [x'' [l'' [Hb_l2 H1]]]]].
			* (* b が l3 に入っている場合１ *) 
				right; left. subst. split; 
				[apply in_eq | apply in_cons; apply in_elt].
			* (* b が l3 に入っている場合２ *) 
				right; left. subst. split; apply in_eq.
			* (* b が l2 に入っている場合 *)
				left. injection H1. intros _ Hb. subst.
				exists [], l2', l''. reflexivity.
	- (* a が l1 に入っている場合 *)
		injection H. intros H1 Ha. subst.
		apply app_split in H1.
		destruct H1 as [[x' [l' [_ Hb_right]]] | [[_ Hb_right] | [x' [l' [Hb_l1 H1]]]]].
		+ (* b が l2 ++ l3 に入っている場合１ *)
			rewrite app_comm_cons in Hb_right. 
			apply app_split in Hb_right.
			destruct Hb_right as [[x'' [l'' [_ Hb_l3]]] | [[_ Hb_l3] | [x'' [l'' [Hb_l2 H1]]]]].
			* (* b が l3 に入っている場合１ *)
				repeat right. subst. exists l1', (l ++ x'' :: l''), l3'. 
				rewrite <- app_assoc. f_equal. simpl. f_equal.
				rewrite <- app_assoc. reflexivity.
			* (* b が l3 に入っている場合２ *) 
				repeat right. subst. exists l1', l, l3'.
				rewrite <- app_assoc. reflexivity.
			* (* b が l2 に入っている場合 *)
				right; right; left. injection H1. intros _ Hb. subst.
				split; apply in_elt.
		+ (* b が l2 ++ l3 に入っている場合２ *)
			destruct l2 as [ | x' l'].
			* (* b が l3 に入っている場合 *)
				repeat right.
				rewrite app_nil_l in Hb_right. subst.
				exists l1', l, l3'.
				rewrite <- app_assoc. reflexivity.
			* (* b が l2 に入っている場合 *)
				right; right; left. injection Hb_right. intros _ Hb. subst.
				split; [apply in_elt | apply in_eq].
		+ (* b が l1 に入っている場合 *)
			repeat right. injection H1. intros _ Hb. subst.
			exists l1', l2', (l' ++ l3).
			rewrite <- app_assoc. f_equal. 
			simpl. f_equal.
			rewrite <- app_assoc. f_equal.
Qed.

Lemma In_order_append_mid : forall {A} (a b : A) l1 l2 l3,
	In_order a b (l1 ++ l3)
	-> In_order a b (l1 ++ l2 ++ l3).
Proof.
	intros A a b l1 l2 l3 H.
	destruct H as [l1' [l2' [l3' E]]].
	(* a, b が l1 に入っているかどうかで場合分け *)
	apply app_split in E.
	destruct E as [[x [l [_ Ha_l3]]] | [[_ Ha_l3] | [x [l [Ha_l1 H]]]]].
	- (* a が l3 に入っている場合１ *)
		subst. 
		exists (l1 ++ l2 ++ x :: l), l2', l3'.
		rewrite <- app_assoc. f_equal.
		rewrite <- app_assoc. f_equal.
	- (* a が l3 に入っている場合２ *)
		subst.
		exists (l1 ++ l2), l2', l3'.
		rewrite <- app_assoc. f_equal.
	- (* a が l1 に入っている場合 *)
		injection H. intros H1 Ha. subst.
		apply app_split in H1.
		destruct H1 as [[x' [l' [_ Hb_l3]]] | [[_ Hb_l3] | [x' [l' [Hb_l1 H1]]]]].
		+ (* b が l3 に入っている場合１ *)
			subst.
			exists l1', (l ++ l2 ++ x' :: l'), l3'.
			rewrite <- app_assoc. f_equal.
			simpl. f_equal.
			rewrite <- app_assoc. f_equal.
			rewrite <- app_assoc. f_equal.
		+ (* b が l3 に入っている場合２ *)
			subst.
			exists l1', (l ++ l2), l3'.
			rewrite <- app_assoc. f_equal.
			simpl. f_equal.
			rewrite <- app_assoc. f_equal.
		+ (* b が l1 に入っている場合 *)
			injection H1. intros _ Hb. subst.
			exists l1', l2', (l' ++ l2 ++ l3).
			rewrite <- app_assoc. f_equal.
			rewrite <- app_comm_cons. f_equal.
			rewrite <- app_assoc. f_equal.
Qed.


(* --------------------------------------------------------------------------- *)
(* Parameter extend に関する補題 *)

Parameter slope_init : Segment -> R. (* 傾きを想定しているが，埋め込みの延長線を一意に定義するものであればよい？ *)
Parameter slope_term : Segment -> R.

Definition hd_segment ls := hd default_segment ls.
Definition last_segment ls := last ls default_segment.

Definition same_init_and_term (c1 c2 : list Segment) := 
	init (hd_segment c1) = init (hd_segment c2) 
	/\ term (last_segment c1) = term (last_segment c2).
Definition same_slope_init_and_term (c1 c2 : list Segment) := 
	slope_init (hd_segment c1) = slope_init (hd_segment c2) 
	/\ slope_term (last_segment c1) = slope_term (last_segment c2).

(* TODO: 空リストを省く *)
Definition onHead (seg: Segment) (rr : R * R) := exists (t:R), t <= 0 /\ point seg t = rr.
Definition onHead_extend (ls: list Segment) (rr : R * R) := onHead (hd_segment ls) rr.
Definition onLast (seg: Segment) (rr : R * R) := exists (t:R), 1 <= t /\ point seg t = rr.
Definition onLast_extend (ls: list Segment) (rr : R * R) := onLast (last_segment ls) rr.
Definition onSegmentlist l rr := exists seg, In seg l /\ onSegment seg rr.
(* TODO: extend に関する公理を完成させた後， onExtendSegment と整合することを確認
		特に空リストの扱い *)
Definition onExtend ls rr := exists t, rr = extend ls t.

Definition same_extention_head ls1 ls2 := 
	(forall rr, onHead_extend ls1 rr <-> onHead_extend ls2 rr).
Definition same_extention_last ls1 ls2 := 
	(forall rr, onLast_extend ls1 rr <-> onLast_extend ls2 rr).

(* 始点と始点での傾きが同じであれば，始点方向への延長線は等しい *)
Lemma same_init_then_same_extention_head : forall ls1 ls2,
	let seg1 := hd_segment ls1 in
	let seg2 := hd_segment ls2 in
	init seg1 = init seg2
	-> slope_init seg1 = slope_init seg2
	-> same_extention_head ls1 ls2.
Proof. 
Admitted.

Lemma same_term_then_same_extention_last : forall ls1 ls2,
	let seg1 := last_segment ls1 in
	let seg2 := last_segment ls2 in
	term seg1 = term seg2
	-> slope_term seg1 = slope_term seg2
	-> same_extention_last ls1 ls2.
Proof. 
Admitted.

(* extend の単調性を公理として導ける？ *)
Lemma extention_split : forall t ls,
	let p := extend ls t in
	ls <> []
	-> (exists t', (* 先頭の延長線上 *)
			t' <= 0 /\ p = point (hd_segment ls) t')
	\/ (exists t' seg, (* セグメント上 *)
			0 <= t' <= 1 /\ In seg ls /\ p = point seg t')
	\/ (exists t', (* 末尾の延長線上 *)
			1 <= t' /\ p = point (last_segment ls) t').
Proof. 
Admitted.

Lemma extention_split_2 : forall t1 t2 ls,
	let p1 := extend ls t1 in
	let p2 := extend ls t2 in
	ls <> []
	-> t1 <> t2
	-> (exists t1' t2', (* t1, t2 とも先頭の延長線上 *)
			t1' <= 0 /\ t2' <= 0 /\ t1' <> t2' /\
				p1 = point (hd_segment ls) t1' /\ p2 = point (hd_segment ls) t2')
	\/ (exists t1' t2' seg, (* t1 は先頭の延長線上， t2 はセグメント上 *)
			t1' <= 0 /\ 0 <= t2' <= 1 /\ In seg ls /\
				p1 = point (hd_segment ls) t1' /\ p2 = point seg t2')
	\/ (exists t1' t2', (* t1 は先頭の延長線上， t2 は末尾の延長線上 *)
			t1' <= 0 /\ 1 <= t2' /\ 
				p1 = point (hd_segment ls) t1' /\ p2 = point (last_segment ls) t2')
	\/ (exists t1' t2' seg, (* t1 はセグメント上， t2 は先頭の延長線上 *)
			0 <= t1' <= 1 /\ t2' <= 0 /\ In seg ls /\
				p1 = point seg t1' /\ p2 = point (hd_segment ls) t2')
	\/ (exists t1' t2' seg, (* t1, t2 とも同じセグメント上 *)
			0 <= t1' <= 1 /\ 0 <= t2' <= 1 /\ t1' <> t2' /\ In seg ls /\
				p1 = point seg t1' /\ p2 = point seg t2')
	\/ (exists t1' t2' seg1 seg2, (* t1, t2 が異なるセグメント上 (t1 < t2) *)
			0 <= t1' <= 1 /\ 0 <= t2' <= 1 /\ In_order seg1 seg2 ls /\
				p1 = point seg1 t1' /\ p2 = point seg2 t2')
	\/ (exists t1' t2' seg1 seg2, (* t1, t2 が異なるセグメント上 (t1 > t2) *)
			0 <= t1' <= 1 /\ 0 <= t2' <= 1 /\ In_order seg2 seg1 ls /\
				p1 = point seg1 t1' /\ p2 = point seg2 t2')
	\/ (exists t1' t2' seg, (* t1 はセグメント上， t2 は末尾の延長線上 *)
			0 <= t1' <= 1 /\ 1 <= t2' /\ In seg ls /\
				p1 = point seg t1' /\ p2 = point (last_segment ls) t2')
	\/ (exists t1' t2', (* t1 は末尾の延長線上， t2 は先頭の延長線上 *)
			1 <= t1' /\ t2' <= 0 /\ 
				p1 = point (last_segment ls) t1' /\ p2 = point (hd_segment ls) t2')
	\/ (exists t1' t2' seg, (* t1 は末尾の延長線上， t2 はセグメント上 *)
			1 <= t1' /\ 0 <= t2' <= 1 /\ In seg ls /\
				p1 = point (last_segment ls) t1' /\ p2 = point seg t2')
	\/ (exists t1' t2', (* t1, t2 とも末尾の延長線上 *)
			1 <= t1' /\ 1 <= t2' /\ t1' <> t2' /\
				p1 = point (last_segment ls) t1' /\ p2 = point (last_segment ls) t2').
Proof. 
	intros t1 t2 ls p1 p2 Hls H12.
	pose proof (extention_split t1 ls Hls) as H1.
	pose proof (extention_split t2 ls Hls) as H2.
	destruct H1 as [[t1' [Ht1' Heq1]] | [[t1' [seg1 [Ht1' [Hin1 Heq1]]]] | [t1' [Ht1' Heq1]]]];
	destruct H2 as [[t2' [Ht2' Heq2]] | [[t2' [seg2 [Ht2' [Hin2 Heq2]]]] | [t2' [Ht2' Heq2]]]].
	- (* t1, t2 とも先頭の延長線上 *) left. 
		exists t1', t2'. repeat split; try tauto.
		(* extend ls t1 = extend ls t1 の場合に証明できない *) admit.
	- (* t1 は先頭の延長線上， t2 はセグメント上 *) right; left. 
		exists t1', t2', seg2. tauto.
	- (* t1 は先頭の延長線上， t2 は末尾の延長線上 *) do 2 right; left.
		exists t1', t2'. tauto.
	- (* t1 はセグメント上， t2 は先頭の延長線上 *) do 3 right; left.
		exists t1', t2', seg1. tauto.
	- (* t1, t2 ともセグメント上 *)
		pose proof (In_split_In_order seg1 seg2 ls Hin1 Hin2) as Hin.
		destruct Hin as [Hin | [Hin | Hin]].
		+ (* t1, t2 とも同じセグメント上 *) do 4 right; left.
			subst. 
		  exists t1', t2', seg2. repeat split; try tauto.
			(* extend ls t1 = extend ls t1 の場合に証明できない *) admit.
		+ (* t1, t2 が異なるセグメント上 (t1 < t2) *) do 5 right; left.
			exists t1', t2', seg1, seg2. tauto.
		+ (* t1, t2 が異なるセグメント上 (t1 > t2) *) do 6 right; left.
			exists t1', t2', seg1, seg2. tauto.
	- (* t1 はセグメント上， t2 は末尾の延長線上 *) do 7 right; left.
		exists t1', t2', seg1. tauto.
	- (* t1 は末尾の延長線上， t2 は先頭の延長線上 *) do 8 right; left.
		exists t1', t2'. tauto.
	- (* t1 は末尾の延長線上， t2 はセグメント上 *) do 9 right; left.
		exists t1', t2', seg2. tauto.
	- (* t1, t2 とも末尾の延長線上 *) repeat right.
		exists t1', t2'. repeat split; try tauto.
		(* extend ls t1 = extend ls t1 の場合に証明できない *) admit.
Admitted.

(* ２つのセグメントが１点を共有していれば，それらのセグメントを含む曲線は閉 *)
Lemma two_segs_have_same_point_close : forall s1 s2 p ls,
	onSegment s1 p
	-> onSegment s2 p
	-> In_order s1 s2 ls (* 逆は不要 *)
	-> close ls.
Proof.
Admitted.

(* 先頭と末尾の延長線が交わっていたら，同じ延長線を持つ曲線は閉 *)
Lemma head_last_cross_close : forall p ls1 ls2,
	onHead_extend ls1 p
	-> onLast_extend ls1 p
	-> same_extention_head ls1 ls2
	-> same_extention_last ls1 ls2
	-> close ls2.
Proof.
Admitted.

(* 先頭の延長線がとあるセグメントと交わっていたら，同じ延長線とセグメントを持つ曲線は閉 *)
Lemma head_seg_cross_close : forall p seg ls1 ls2,
	onHead_extend ls1 p
	-> In seg ls1
	-> onSegment seg p
	-> same_extention_head ls1 ls2
	-> In seg ls2
	-> close ls2.
Proof.
Admitted.

(* 末尾の延長線がとあるセグメントと交わっていたら，同じ延長線とセグメントを持つ曲線は閉 *)
Lemma last_seg_cross_close : forall p seg ls1 ls2,
	onLast_extend ls1 p
	-> In seg ls1
	-> onSegment seg p
	-> same_extention_last ls1 ls2
	-> In seg ls2
	-> close ls2.
Proof.
Admitted.

(* １つのセグメントの中（延長部分含め）で交差は起こらない *)
Lemma one_seg_not_cross : forall t1 t2 seg,
	point seg t1 = point seg t2
	-> t1 = t2.
Proof.
Admitted.


(* --------------------------------------------------------------------------- *)
(* AdmissibleDirs について成り立ってほしい性質と，それに必要な補題 *)

Parameter default_primitive_segment : PrimitiveSegment.
Definition hd_scurve (sc: scurve) := hd default_primitive_segment (proj1_sig sc).

Lemma one_pseg_is_scurve : forall (p: PrimitiveSegment), 
	is_scurve [p].
Proof. 
	intros p. apply IsScurveCons.
	- apply IsScurveNil.
	- apply DcNil.
Qed.
	
Definition scurve_from_one p := exist _ _ (one_pseg_is_scurve p).

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
	(１つの scurve で許容可能性が言えたら，同じ向き列を持つ他の scurve ４つの許容可能性もわかる．) *)
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


(* --------------------------------------------------------------------------- *)
(* 許容可能性保持の証明に向けた定義と補題群 *)

Definition embed_listDir (ds: list Direction) (ls: list Segment) : Prop :=
	exists sc: scurve, scurve_to_direction sc = ds
	/\ embed_scurve sc ls.

(* 単方向 scurve *)
(* cf. Embed.all_same_h *)
(* TODO: 空リストは含まない．（含めるなら，後の定理の必要な部分に not nil 制約を入れる．） *)
Definition is_one_way_scurve (sc : scurve) : Prop :=
	let lp := proj1_sig sc in
	lp <> []
	/\ (Forall (fun p => exists (v:V) (c:C), p = (v, e, c)) lp
	\/ Forall (fun p => exists (v:V) (c:C), p = (v, w, c)) lp
	\/ Forall (fun p => exists (h:H) (c:C), p = (n, h, c)) lp
	\/ Forall (fun p => exists (h:H) (c:C), p = (s, h, c)) lp).

Definition is_one_way_embedding (ls : list Segment) : Prop :=
	exists sc, embed_scurve sc ls /\ is_one_way_scurve sc.
Definition is_one_way_listDir (ds: list Direction) : Prop :=
	exists sc: scurve, scurve_to_direction sc = ds /\ is_one_way_scurve sc.
(* おそらく帰納的に定義することもできる．後者は回転数を使った定義もできる？
		必要があれば証明 *)

(* 曲線の始点と終点を結んだ線分を対角線にもつ矩形．部分曲線を含むとは限らない *)
Parameter rectangular_from_diagonal : R * R -> R * R -> (R * R -> Prop).
Definition in_rect_from_diagonal a b rr := rectangular_from_diagonal a b rr.
(* TODO: 空リストを含まない方が良い *)
Definition in_rect (ls: list Segment) (rr: R * R) := 
	in_rect_from_diagonal (init (hd_segment ls)) (term (last_segment ls)) rr.

(* scurve の埋め込みが sub_ls 周りで疎 := sub_ls の始点と終点から作成できる矩形に全然関係ないセグメントが侵入してこない
		sub_ls が開か，全体として開埋め込みかは知らない *)
Definition is_sparse_embedding (sc : scurve) (l sub_ls r : list Segment) : Prop :=
	let ls := l ++ sub_ls ++ r in
	embed_scurve sc ls
	/\ (forall rr, 
			(onHead_extend ls rr \/ onSegmentlist l rr \/ onSegmentlist r rr \/ onLast_extend ls rr) 
			-> ~ in_rect sub_ls rr).

Definition sparse (l sub_ls r : list Segment) : Prop :=
	exists sc, is_sparse_embedding sc l sub_ls r.


Lemma is_one_way_listDir_forall : forall ds,
	is_one_way_listDir ds <-> 
		(forall sc, scurve_to_direction sc = ds -> is_one_way_scurve sc).
Proof.
Admitted. 

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

Lemma embedding_oneway_listDir : forall ds ls, 
	embed_listDir ds ls -> is_one_way_listDir ds -> is_one_way_embedding ls.
Proof.
	intros ds ls H1 H2.
	destruct H1 as [sc [Hdir Hembed]].
	exists sc. split; auto.
	apply (is_one_way_listDir_forall ds); auto.
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

Lemma embedding_listDir_length_consis: forall (ds: list Direction) (ls: list Segment),
  embed_listDir ds ls -> length ds = length ls.
Proof.
	intros ds ls [sc [Hdir Hembed]].
	rewrite (scurve_listDir_length_consis _ _ Hdir).
	apply scurve_length_consis.
	auto.
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

(* sub_ls 周りで疎な埋め込みについて， sub_ls を矩形の中で sub_ls' に変えても疎なまま *)
Lemma sparse_in_rect_change : forall (ls rs sub_ls sub_ls' : list Segment), 
	sparse ls sub_ls rs
	-> (forall rr, onSegmentlist sub_ls' rr -> in_rect sub_ls rr) 
	-> same_init_and_term sub_ls sub_ls' 
	-> same_slope_init_and_term sub_ls sub_ls'
	-> sparse ls sub_ls' rs.
Proof. 
Admitted.


(*【証明の本質としている補題１】 許容可能ならば，その中の単方向な sub_ds の埋め込み sub_ls 周りで疎な開埋め込みが存在する *)
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
Proof. Admitted.

(* TODO：some good features を具体化（引数要るだろう）して上の補題に統合する
		sub_ls の始点と終点とそれぞれでの傾きを（sub_ls の向きを考慮した上で）自由に選んでも良い，
		としたらのちに端点での傾きを保存するために役立つ？  *)
Parameter some_good_features : Prop.

Lemma embed_sparsely_listDir_with_good_features (ds1 sub_ds ds2 : list Direction) :
	AdmissibleDirs (ds1 ++ sub_ds ++ ds2)
	-> is_one_way_listDir sub_ds
	-> exists l r sub_ls, 
		embed_listDir ds1 l
		/\ embed_listDir sub_ds sub_ls
		/\ embed_listDir ds2 r
		/\ embed_listDir (ds1 ++ sub_ds ++ ds2) (l ++ sub_ls ++ r)
		/\ ~ close (l ++ sub_ls ++ r)
		/\ sparse l sub_ls r
		/\ some_good_features.
Proof. Admitted.

(* Plus (の向きを持つ Primitive Segment) の埋め込みを，端点とそこでの傾きを保存したまま
		[Plus; Minus; Plus] の埋め込みとなる３つに矩形内で分割できる *)
Lemma embedding_P_to_PMP_in_rect : forall (seg : Segment),
	embed_listDir [Plus] [seg]
	-> exists seg1 seg2 seg3,
		embed_listDir [Plus; Minus; Plus] [seg1; seg2; seg3] (* この内部で seg1-3 が連結していることは示されてほしい *)
		/\ (forall rr, onSegmentlist [seg1; seg2; seg3] rr
				-> in_rect [seg] rr) (* seg が張る矩形の内部で分割できている *)
		/\ same_init_and_term [seg] [seg1; seg2; seg3]
		/\ same_slope_init_and_term [seg] [seg1; seg2; seg3].
Proof. Admitted.

(* [Plus; Minus] の埋め込みを，端点とそこでの傾きを保存したまま
		[Plus; Plus; Minus; Minus] の埋め込みとなる4つに矩形内で分割できる *)
Lemma embedding_PM_to_PPMM_in_rect : forall (seg1 seg2 : Segment),
	embed_listDir [Plus; Minus] [seg1; seg2]
	-> exists seg1' seg2' seg3' seg4',
		embed_listDir [Plus; Plus; Minus; Minus] [seg1'; seg2'; seg3'; seg4'] (* この内部で seg1-3 が連結していることは示されてほしい *)
		/\ (forall rr, onSegmentlist [seg1'; seg2'; seg3'; seg4'] rr
				-> in_rect [seg1; seg2] rr) (* seg が張る矩形の内部で分割できている *)
		/\ same_init_and_term [seg1; seg2] [seg1'; seg2'; seg3'; seg4']
		/\ same_slope_init_and_term [seg1; seg2] [seg1'; seg2'; seg3'; seg4'].
Proof. Admitted.

(* good features があれば，[Plus; Minus; Plus] の埋め込みを， 端点とそこでの傾きを保存したまま
		Plus の埋め込みに矩形内で変更できる *)
(* TODO：傾きも保存できるような good features を見つけて具体化 *)
Lemma embedding_PMP_to_P_in_rect : forall (seg1 seg2 seg3 : Segment),
	some_good_features
	-> embed_listDir [Plus; Minus; Plus] [seg1; seg2; seg3]
	->
	exists seg,
		embed_listDir [Plus] [seg]
		/\ (forall rr, onSegment seg rr
				-> in_rect [seg1; seg2; seg3] rr ) (* seg が張る矩形の内部で分割できている *)
		/\ same_init_and_term [seg1; seg2; seg3] [seg]
		/\ same_slope_init_and_term [seg1; seg2; seg3] [seg].
Proof. Admitted.

(* good features があれば，[Plus; Plus; Minus; Minus] の埋め込みを，端点とそこでの傾きを保存したまま
		[Plus; Minus] の埋め込みとなる2つに矩形内で分割できる *)
(* TODO：傾きも保存できるような good features を見つけて具体化 *)
Lemma embedding_PPMM_to_PM_in_rect : forall (seg1 seg2 seg3 seg4 : Segment),
	some_good_features
	-> embed_listDir [Plus; Plus; Minus; Minus] [seg1; seg2; seg3; seg4]
	->
	exists seg1' seg2',
		embed_listDir [Plus; Minus] [seg1'; seg2'] 
		/\ (forall rr, onSegmentlist [seg1'; seg2'] rr
				-> in_rect [seg1; seg2; seg3; seg4] rr) (* seg が張る矩形の内部で分割できている *)
		/\ same_init_and_term [seg1; seg2; seg3; seg4] [seg1'; seg2']
		/\ same_slope_init_and_term [seg1; seg2; seg3; seg4] [seg1'; seg2'].
Proof. Admitted.

(*  向き ds1 ++ ds2 ++ ds3 の ds2 (の向きを持つ scurve) の埋め込みを，ds2' の埋め込みに変えたら，
		向き ds1 ++ ds2' ++ ds3 の埋め込みである *)
(* TODO: 向き列を交えず scurve だけでいけばコンパクトに，もし hd_scurve 取れればきれい？ *)
Lemma embbeding_inner_change : forall sc1 sc2 ds1 ds2 ds2' ds3 ls1 ls2 ls2' ls3,
	ls2 <> []
	-> ls2' <> []
	-> embed_scurve sc1 (ls1 ++ ls2 ++ ls3) (* つまり ls1, ls2, ls3 は繋がっている *)
	-> embed_listDir ds2 ls2
	-> embed_listDir ds2' ls2'
	-> same_init_and_term ls2 ls2'
	-> scurve_to_direction sc1 = ds1 ++ ds2 ++ ds3
	-> scurve_to_direction sc2 = ds1 ++ ds2' ++ ds3
	-> hd_scurve sc1 = hd_scurve sc2
	-> embed_scurve sc2 (ls1 ++ ls2' ++ ls3).
Proof. Admitted.

(* 【証明の本質としている補題２】 sub_ls の周りが疎な開埋め込みにおいて，端点で傾きを保ちつつ
		sub_ls をその領域に収まる開な sub_ls' に置き換えても開のまま *)
Lemma seg_in_rectangle_keep_openness : forall (ls rs sub_ls sub_ls' : list Segment),
	sub_ls <> []
	-> sub_ls' <> [] 
	-> ~ close sub_ls'
	-> ~ close (ls ++ sub_ls ++ rs)
	-> sparse ls sub_ls rs
	-> (forall rr, onSegmentlist sub_ls' rr -> in_rect sub_ls rr) 
	-> same_init_and_term sub_ls sub_ls' 
	-> same_slope_init_and_term sub_ls sub_ls'
	-> ~ close (ls ++ sub_ls' ++ rs).
Proof. 
	intros ls rs sub_ls sub_ls' Hsub Hsub' Hopen' Hopen Hsparse Hin_rect Hinit_term Hslope Hclose.
	destruct Hclose as [t1 [t2 [H12 Hsame]]].
	(* ls ++ sub_ls' ++ rs が t1, t2 の表す点で自己交差しているとして矛盾を導く *)
	set (pre := ls ++ sub_ls ++ rs). 
	set (post := ls ++ sub_ls' ++ rs).
	set (intersection := extend post t1).
	assert (H_notnil : post <> []). {
		intros H. subst post.
		apply app_eq_nil in H. 
		destruct H as [_ H].
		apply app_eq_nil in H. 
		destruct H as [H _].
		contradiction.
	}
	assert (Hsub_hd: hd_segment sub_ls = hd_segment (sub_ls ++ rs)). {
		apply hd_app. assumption.
	}
	assert (Hsub_hd': hd_segment sub_ls' = hd_segment (sub_ls' ++ rs)). {
		apply hd_app. assumption.
	}
	assert (Hsub_last: last_segment sub_ls = last_segment (ls ++ sub_ls)). {
		apply last_app. assumption.
	}
	assert (Hsub_last': last_segment sub_ls' = last_segment (ls ++ sub_ls')). {
		apply last_app. assumption.
	}
	(* 変換前後で延長線部分が変化しない *)
	assert (Hsame_ex_head : same_extention_head post pre). {
		destruct Hinit_term. destruct Hslope.
		subst pre post.
		destruct ls.
		- (* ls = [] *)
			simpl.
			apply same_init_then_same_extention_head;
			rewrite <- Hsub_hd; rewrite <- Hsub_hd'; auto.
		- (* ls <> [] *) 
			apply same_init_then_same_extention_head; reflexivity.
	}
	assert (Hsame_ex_last : same_extention_last post pre). {
		destruct Hinit_term. destruct Hslope.
		subst pre post.
		destruct rs.
		- (* rs = [] *)
			repeat rewrite app_nil_r.
			apply same_term_then_same_extention_last;
			rewrite <- Hsub_last; rewrite <- Hsub_last'; auto.
		- (* rs <> [] *) 
			apply same_term_then_same_extention_last; 
			repeat rewrite app_assoc;
			unfold last_segment;
			repeat rewrite last_app_cons; reflexivity.
	}

	(* t1, t2 の表す位置について場合分け *)
	destruct (extention_split_2 t1 t2 post H_notnil H12) as [
			(* t1 が先頭を指す場合 *)
				[t1' [t2' [H1' [H2' [H12' [Heq1 Heq2]]]]]]
			| [[t1' [t2' [seg [H1' [H2' [Hin_post [Heq1 Heq2]]]]]]]
			| [[t1' [t2' [H1' [H2' [Heq1 Heq2]]]]]
			(* t1 がセグメント上の点を指す場合 *)
			| [[t1' [t2' [seg [H1' [H2' [Hin_post [Heq1 Heq2]]]]]]]
			| [[t1' [t2' [seg [H1' [H2' [H12' [Hin_post [Heq1 Heq2]]]]]]]]
			| [[t1' [t2' [seg1 [seg2 [H1' [H2' [Hin_post [Heq1 Heq2]]]]]]]]
			| [[t1' [t2' [seg1 [seg2 [H1' [H2' [Hin_post [Heq1 Heq2]]]]]]]]
			| [[t1' [t2' [seg [H1' [H2' [Hin_post [Heq1 Heq2]]]]]]]
			(* t1 が末尾を指す場合 *)
			| [[t1' [t2' [H1' [H2' [Heq1 Heq2]]]]]
			| [[t1' [t2' [seg [H1' [H2' [Hin_post [Heq1 Heq2]]]]]]]
			| [t1' [t2' [H1' [H2' [H12' [Heq1 Heq2]]]]]]]]]]]]]]]].
		(* 似ている場合分けばっかりなので，まとめて処理したいが．．． *)

		- (* t1, t2 ともに先頭の延長線上の点を指す場合：矛盾 *)
			apply H12'.
			apply (one_seg_not_cross _ _ (hd_segment post)). subst post; congruence.

		- (* t1 が先頭の延長線上の点を， t2 がセグメント上の点を指す場合：セグメントがそれぞれ pre, sub_ls' どちらに属するかで場合分け *) 
			assert (Hin : In seg pre \/ In seg sub_ls'). {
				apply in_app_or in Hin_post as [Hin_ls | Hin_rest]. 
				* left. apply in_or_app. auto. 
				* apply in_app_or in Hin_rest as [Hin_subls' | Hin_rs]; auto.
					left. apply in_or_app. right. apply in_or_app. auto. 
			} 
			destruct Hin as [Hin | Hin]. 
			+ (* 先頭の延長線と ls(rs) が交わっている場合： pre が開であることに矛盾 *) 
				apply Hopen.
				apply (head_seg_cross_close intersection seg post); auto. 
				-- exists t1'. split; subst post intersection; congruence. 
				-- exists t2'. split; subst post intersection; congruence. 
			+ (* 先頭の延長線と sub_ls' が交わっている場合： pre が疎であることに矛盾 *) 
				assert (Hin_rect_yes : in_rect sub_ls intersection). {
					apply Hin_rect. exists seg. split; auto.
					exists t2'. split; subst post intersection; congruence. 
				}
				assert (Hin_rect_no : ~ in_rect sub_ls intersection). {
					destruct Hsparse as [sc [_ Hsparse]].
					apply Hsparse.
					left.
					apply Hsame_ex_head. 
					exists t1'. split; subst post intersection; congruence. 
				} 
				auto.

		- (* t1 が先頭の延長線上の点を， t2 が末尾の延長線上の点を指す場合： pre が開であることに矛盾 *)
			apply Hopen. 
			apply (head_last_cross_close intersection post); auto.
			* exists t1'. split; subst post intersection; congruence. 
			* exists t2'. split; subst post intersection; congruence. 

		- (* t1 がセグメント上の点を， t2 が先頭の延長線上の点を指す場合：セグメントがそれぞれ pre, sub_ls' どちらに属するかで場合分け *) 
			assert (Hin : In seg pre \/ In seg sub_ls'). {
				apply in_app_or in Hin_post as [Hin_ls | Hin_rest]. 
				* left. apply in_or_app. auto. 
				* apply in_app_or in Hin_rest as [Hin_subls' | Hin_rs]; auto.
					left. apply in_or_app. right. apply in_or_app. auto. 
			} 
			destruct Hin as [Hin | Hin]. 
			+ (* 先頭の延長線と ls(rs) が交わっている場合： pre が開であることに矛盾 *) 
				apply Hopen.
				apply (head_seg_cross_close intersection seg post); auto. 
				-- exists t2'. split; subst post intersection; congruence. 
				-- exists t1'. split; subst post intersection; congruence. 
			+ (* 先頭の延長線と sub_ls' が交わっている場合： pre が疎であることに矛盾 *) 
				assert (Hin_rect_yes : in_rect sub_ls intersection). {
					apply Hin_rect. exists seg. split; auto.
					exists t1'. split; subst post intersection; congruence. 
				}
				assert (Hin_rect_no : ~ in_rect sub_ls intersection). {
					destruct Hsparse as [sc [_ Hsparse]].
					apply Hsparse.
					left.
					apply Hsame_ex_head. 
					exists t2'. split; subst post intersection; congruence. 
				} 
				auto.

		- (* t1, t2 が同じセグメント上の点を指す場合：矛盾 *) 
			apply H12'.
			apply (one_seg_not_cross _ _ seg). subst post; congruence.

		- (* t1, t2 が異なるセグメント上の点を指す場合１：２つのセグメントがそれぞれ pre, sub_ls' どちらに属するかで場合分け *) 
			assert (Hin : (In_order seg1 seg2 sub_ls') 
				\/ (In seg1 sub_ls' /\ In seg2 rs)
				\/ (In seg1 ls /\ In seg2 sub_ls')
				\/ In_order seg1 seg2 (ls ++ rs)). {
					apply In_order_split.
					auto.
			}
			destruct Hin as [Hin | [Hin | [Hin | Hin]]]. 
			+ (* 両方 sub_ls' 上の点である場合： sub_ls' が開であることに矛盾 *) 
				apply Hopen'.
				apply (two_segs_have_same_point_close seg1 seg2 intersection). 
				-- exists t1'. split; subst post intersection; congruence. 
				-- exists t2'. split; subst post intersection; congruence. 
				-- auto.
			+ (* １つが pre 上の点，もう１つが sub_ls' 上の点の場合１： pre が疎であることに矛盾 *) 
				assert (Hin_rect_yes : in_rect sub_ls intersection). {
					destruct Hin.
					apply Hin_rect. exists seg1. split; auto.
					exists t1'. split; subst post intersection; congruence. 
				}
				assert (Hin_rect_no : ~ in_rect sub_ls intersection). {
					destruct Hin.
					destruct Hsparse as [sc [_ Hsparse]].
					apply Hsparse.
					right. right. left.
					exists seg2. split; auto.
					exists t2'. split; auto. subst post intersection; congruence. 
				} 
				auto.
			+ (* １つが pre 上の点，もう１つが sub_ls' 上の点の場合２： pre が疎であることに矛盾 *) 
				assert (Hin_rect_yes : in_rect sub_ls intersection). {
					destruct Hin.
					apply Hin_rect. exists seg2. split; auto.
					exists t2'. split; subst post intersection; congruence. 
				}
				assert (Hin_rect_no : ~ in_rect sub_ls intersection). {
					destruct Hin.
					destruct Hsparse as [sc [_ Hsparse]].
					apply Hsparse.
					right. left.
					exists seg1. split; auto.
					exists t1'. split; auto.
				} 
				auto.
			+ (* 両方 pre 上の点である場合： pre が開であることに矛盾 *) 
				apply Hopen.
				apply (two_segs_have_same_point_close seg1 seg2 intersection). 
				-- exists t1'. split; subst post intersection; congruence. 
				-- exists t2'. split; subst post intersection; congruence. 
				-- apply In_order_append_mid. auto.

		- (* t1, t2 が異なるセグメント上の点を指す場合２：２つのセグメントがそれぞれ pre, sub_ls' どちらに属するかで場合分け *) 
			assert (Hin : (In_order seg2 seg1 sub_ls') 
				\/ (In seg2 sub_ls' /\ In seg1 rs)
				\/ (In seg2 ls /\ In seg1 sub_ls')
				\/ In_order seg2 seg1 (ls ++ rs)). {
					apply In_order_split.
					auto.
			}
			destruct Hin as [Hin | [Hin | [Hin | Hin]]]. 
			+ (* 両方 sub_ls' 上の点である場合： sub_ls' が開であることに矛盾 *) 
				apply Hopen'.
				apply (two_segs_have_same_point_close seg2 seg1 intersection). 
				-- exists t2'. split; subst post intersection; congruence. 
				-- exists t1'. split; subst post intersection; congruence. 
				-- auto.
			+ (* １つが pre 上の点，もう１つが sub_ls' 上の点の場合１： pre が疎であることに矛盾 *) 
				assert (Hin_rect_yes : in_rect sub_ls intersection). {
					destruct Hin.
					apply Hin_rect. exists seg2. split; auto.
					exists t2'. split; subst post intersection; congruence. 
				}
				assert (Hin_rect_no : ~ in_rect sub_ls intersection). {
					destruct Hin.
					destruct Hsparse as [sc [_ Hsparse]].
					apply Hsparse.
					right. right. left.
					exists seg1. split; auto.
					exists t1'. split; auto. 
				} 
				auto.
			+ (* １つが pre 上の点，もう１つが sub_ls' 上の点の場合２： pre が疎であることに矛盾 *) 
				assert (Hin_rect_yes : in_rect sub_ls intersection). {
					destruct Hin.
					apply Hin_rect. exists seg1. split; auto.
					exists t1'. split; subst post intersection; congruence. 
				}
				assert (Hin_rect_no : ~ in_rect sub_ls intersection). {
					destruct Hin.
					destruct Hsparse as [sc [_ Hsparse]].
					apply Hsparse.
					right. left.
					exists seg2. split; auto.
					exists t2'. split; auto. subst post intersection; congruence.
				} 
				auto.
			+ (* 両方 pre 上の点である場合： pre が開であることに矛盾 *) 
				apply Hopen.
				apply (two_segs_have_same_point_close seg2 seg1 intersection). 
				-- exists t2'. split; subst post intersection; congruence. 
				-- exists t1'. split; subst post intersection; congruence. 
				-- apply In_order_append_mid. auto.

		- (* t1 がセグメント上の点を， t2 が末尾の延長線上の点を指す場合：セグメントがそれぞれ pre, sub_ls' どちらに属するかで場合分け *)
		  assert (Hin : In seg pre \/ In seg sub_ls'). {
				apply in_app_or in Hin_post as [Hin_ls | Hin_rest]. 
				* left. apply in_or_app. auto. 
				* apply in_app_or in Hin_rest as [Hin_subls' | Hin_rs]; auto.
					left. apply in_or_app. right. apply in_or_app. auto. 
			} 
			destruct Hin as [Hin | Hin]. 
			* (* 末尾の延長線と ls(rs) が交わっている場合： pre が開であることに矛盾 *) 
				apply Hopen.
				apply (last_seg_cross_close intersection seg post); auto. 
				-- exists t2'. split; subst post intersection; congruence. 
				-- exists t1'. split; subst post intersection; congruence. 
			* (* 末尾の延長線と sub_ls' が交わっている場合： pre が疎であることに矛盾 *) 
				assert (Hin_rect_yes : in_rect sub_ls intersection). {
					apply Hin_rect. exists seg. split; auto.
					exists t1'. split; subst post intersection; congruence. 
				}
				assert (Hin_rect_no : ~ in_rect sub_ls intersection). {
					destruct Hsparse as [sc [_ Hsparse]].
					apply Hsparse.
					repeat right.
					apply Hsame_ex_last. 
					exists t2'. split; subst post intersection; congruence. 
				} 
				auto.

		- (* t1 が末尾の延長線上の点を， t2 が先頭の延長線上の点を指す場合： pre が開であることに矛盾 *)
			apply Hopen. 
			apply (head_last_cross_close intersection post); auto.
			* exists t2'. split; subst post intersection; congruence. 
			* exists t1'. split; subst post intersection; congruence. 

		- (* t1 が末尾の延長線上の点を， t2 がセグメント上の点を指す場合：セグメントがそれぞれ pre, sub_ls' どちらに属するかで場合分け *)
		  assert (Hin : In seg pre \/ In seg sub_ls'). {
				apply in_app_or in Hin_post as [Hin_ls | Hin_rest]. 
				* left. apply in_or_app. auto. 
				* apply in_app_or in Hin_rest as [Hin_subls' | Hin_rs]; auto.
					left. apply in_or_app. right. apply in_or_app. auto. 
			} 
			destruct Hin as [Hin | Hin]. 
			* (* 末尾の延長線と ls(rs) が交わっている場合： pre が開であることに矛盾 *) 
				apply Hopen.
				apply (last_seg_cross_close intersection seg post); auto. 
				-- exists t1'. split; subst post intersection; congruence. 
				-- exists t2'. split; subst post intersection; congruence. 
			* (* 末尾の延長線と sub_ls' が交わっている場合： pre が疎であることに矛盾 *) 
				assert (Hin_rect_yes : in_rect sub_ls intersection). {
					apply Hin_rect. exists seg. split; auto.
					exists t2'. split; subst post intersection; congruence. 
				}
				assert (Hin_rect_no : ~ in_rect sub_ls intersection). {
					destruct Hsparse as [sc [_ Hsparse]].
					apply Hsparse.
					repeat right.
					apply Hsame_ex_last. 
					exists t1'. split; subst post intersection; congruence. 
				} 
				auto.

		- (* t1, t2 ともに末尾の延長線上の点を指す場合：矛盾 *) 
			apply H12'.
			apply (one_seg_not_cross _ _ (last_segment post)). subst post; congruence.
Qed.


(* --------------------------------------------------------------------------- *)
(* 許容可能性保持に関する主張８つと，その系 *)

(* [+-+ => +] での簡約で，簡約元が許容可能なら簡約先も許容可能 *)
Lemma AdmissibleDirs_r1_Plus: forall l r,
  AdmissibleDirs (l ++ [Plus; Minus; Plus] ++ r) -> AdmissibleDirs (l ++ [Plus] ++ r).
Proof.
	intros l r admds. 
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely_listDir_with_good_features _ _ _ admds PMP_is_oneway) 
		as [ls1 [ls3 [ls2 [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [Hopen [Hsparse Hgood]]]]]]]]];
	simpl in *.
	assert (Hdir: hd Plus (l ++ Plus :: r) = orn (hd_scurve sc)). {
		unfold hd_scurve. unfold scurve_to_direction in Hdir_sc.
		destruct l; simpl in *;
		symmetry; eapply list_map_head; apply Hdir_sc.
	}
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Plus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Plus; Minus; Plus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_head_tail. destruct l; discriminate.
	- (* 許容可能であること *)
		assert (H: embed_listDir (l ++ [Plus; Minus; Plus] ++ r) (ls1 ++ ls2 ++ ls3)). { (* scurve ではなく向き列の方が扱いやすい *)
			unfold embed_listDir. exists sc. split; assumption.
		}
		pose proof (embedding_three_dir Plus Minus Plus ls2 Hls2) as [seg1 [seg2 [seg3 HPMP]]]; subst.
		pose proof (embedding_PMP_to_P_in_rect seg1 seg2 seg3 Hgood Hls2) as [segP [HP [Hin_rect [Hinit_term Hslope]]]].
		(* 欲しかった埋め込み *) 
		exists (ls1 ++ [segP] ++ ls3). 
		unfold admissible. 
		split.
		+ (* 埋め込みになっていること *) 
			apply (embbeding_inner_change sc sc' l [Plus; Minus; Plus] [Plus] r ls1 [seg1; seg2; seg3] [segP] ls3); 
				try assumption; try discriminate.
			(* 仮定を満たすことはほぼ作業的に示せる *)
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_head_tail. destruct l; discriminate.
			* symmetry. assumption.
		+ (* その埋め込みが開であること *) 
			apply (seg_in_rectangle_keep_openness _ _ [seg1; seg2; seg3] [segP]); 
				try assumption; try (symmetry; assumption); try congruence.
			(* 残った subgoal もほぼ自明 *)
			* apply oneway_then_open. apply (embedding_oneway_listDir [Plus]); try assumption.
				apply P_is_oneway.
			* intros rr [seg' [H1 H2]]. apply Hin_rect.
				destruct H1; [subst; assumption | exfalso; assumption].
Qed.

Lemma AdmissibleDirs_r1_Minus: forall l r,
  AdmissibleDirs (l ++ [Minus; Plus; Minus] ++ r) -> AdmissibleDirs (l ++ [Minus] ++ r).
Proof.
Admitted.

(* [+-+ => +] での簡約で，簡約先が許容可能ならもともと許容可能 *)
Lemma AdmissibleDirs_r1_Plus_inv: forall l r,
  AdmissibleDirs (l ++ [Plus] ++ r) -> AdmissibleDirs (l ++ [Plus; Minus; Plus] ++ r).
Proof.
	intros l r admds. 
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely_listDir _ _ _ admds P_is_oneway) 
		as [ls1 [ls3 [ls2 [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [Hopen Hsparse]]]]]]]];
	simpl in *.
	assert (Hdir: hd Plus (l ++ Plus :: Minus :: Plus :: r) = orn (hd_scurve sc)). {
		unfold hd_scurve. unfold scurve_to_direction in Hdir_sc.
		destruct l; simpl in *;
		symmetry; eapply list_map_head; apply Hdir_sc.
	}	
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Plus :: Minus :: Plus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Plus; Minus; Plus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_head_tail. destruct l; discriminate.
	- (* 許容可能であること *)
		assert (H: embed_listDir (l ++ [Plus] ++ r) (ls1 ++ ls2 ++ ls3)). { (* scurve ではなく向き列の方が扱いやすい *)
			unfold embed_listDir. exists sc. split; assumption.
		}
		pose proof (embedding_one_dir Plus ls2 Hls2) as [segP HP]; subst.
		pose proof (embedding_P_to_PMP_in_rect segP Hls2) 
			as [seg1 [seg2 [seg3 [HPMP [Hin_rect [Hinit_term Hslope]]]]]].
		(* 欲しかった埋め込み *) 
		exists (ls1 ++ [seg1; seg2; seg3] ++ ls3). 
		unfold admissible. 
		split.
		+ (* 埋め込みになっていること *) 
			apply (embbeding_inner_change sc sc' l [Plus] [Plus; Minus; Plus] r ls1 [segP] [seg1; seg2; seg3] ls3); 
				try assumption; try discriminate.
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_head_tail. destruct l; discriminate.
			* symmetry. assumption.
		+ (* その埋め込みが開であること *) 
			apply (seg_in_rectangle_keep_openness _ _ [segP] _ ); try assumption; try congruence.
			* apply oneway_then_open. apply (embedding_oneway_listDir [Plus; Minus; Plus]); try assumption.
				apply PMP_is_oneway.
Qed.

Lemma AdmissibleDirs_r1_Minus_inv: forall l r,
  AdmissibleDirs (l ++ [Minus] ++ r) -> AdmissibleDirs (l ++ [Minus; Plus; Minus] ++ r).
Proof.
Admitted.

Lemma AdmissibleDirs_r2_Plus: forall l r,
  AdmissibleDirs (l ++ [Plus; Plus; Minus; Minus] ++ r) -> AdmissibleDirs (l ++ [Plus; Minus] ++ r).
Proof.
	intros l r admds. 
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely_listDir_with_good_features _ _ _ admds PPMM_is_oneway) 
		as [ls1 [ls3 [ls2 [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [Hopen [Hsparse Hgood]]]]]]]]];
	simpl in *.
	assert (Hdir: hd Plus (l ++ Plus :: Minus :: r) = orn (hd_scurve sc)). {
		unfold hd_scurve. unfold scurve_to_direction in Hdir_sc.
		destruct l; simpl in *;
		symmetry; eapply list_map_head; apply Hdir_sc.
	}
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Plus :: Minus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Plus; Minus; Plus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_head_tail. destruct l; discriminate.
	- (* 許容可能であること *)
		assert (H: embed_listDir (l ++ [Plus; Plus; Minus; Minus] ++ r) (ls1 ++ ls2 ++ ls3)). { (* scurve ではなく向き列の方が扱いやすい *)
			unfold embed_listDir. exists sc. split; assumption.
		}
		pose proof (embedding_four_dir Plus Plus Minus Minus ls2 Hls2) as [seg1 [seg2 [seg3 [seg4 HPPMM]]]]; subst.
		pose proof (embedding_PPMM_to_PM_in_rect seg1 seg2 seg3 seg4 Hgood Hls2) 
			as [seg1' [seg2' [HPM [Hin_rect [Hinit_term Hslope]]]]].
		(* 欲しかった埋め込み *) 
		exists (ls1 ++ [seg1'; seg2'] ++ ls3). 
		unfold admissible. 
		split.
		+ (* 埋め込みになっていること *) 
			apply (embbeding_inner_change sc sc' l [Plus; Plus; Minus; Minus] [Plus; Minus] r ls1 [seg1; seg2; seg3; seg4] [seg1'; seg2'] ls3); 
				try assumption; try discriminate.
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_head_tail. destruct l; discriminate.
			* symmetry. assumption.
		+ (* その埋め込みが開であること *) 
			apply (seg_in_rectangle_keep_openness _ _ [seg1; seg2; seg3; seg4] [seg1'; seg2']); 
				try assumption; try (symmetry; assumption); try congruence.
			* apply oneway_then_open. apply (embedding_oneway_listDir [Plus; Minus]); try assumption.
			apply PM_is_oneway.
Qed.

Lemma AdmissibleDirs_r2_Minus: forall l r,
  AdmissibleDirs (l ++ [Minus; Minus; Plus; Plus] ++ r) -> AdmissibleDirs (l ++ [Minus; Plus] ++ r).
Proof.
Admitted.

Lemma AdmissibleDirs_r2_Plus_inv: forall l r,
  AdmissibleDirs (l ++ [Plus; Minus] ++ r) -> AdmissibleDirs (l ++ [Plus; Plus; Minus; Minus] ++ r).
Proof.
	intros l r admds. 
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely_listDir _ _ _ admds PM_is_oneway) 
		as [ls1 [ls3 [ls2 [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [Hopen Hsparse]]]]]]]];
	simpl in *.
	assert (Hdir: hd Plus (l ++ Plus :: Plus :: Minus :: Minus :: r) = orn (hd_scurve sc)). {
		unfold hd_scurve. unfold scurve_to_direction in Hdir_sc.
		destruct l; simpl in *;
		symmetry; eapply list_map_head; apply Hdir_sc.
	}	
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Plus :: Plus :: Minus :: Minus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Plus; Minus; Plus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_head_tail. destruct l; discriminate.
	- (* 許容可能であること *)
		assert (H: embed_listDir (l ++ [Plus; Minus] ++ r) (ls1 ++ ls2 ++ ls3)). { (* scurve ではなく向き列の方が扱いやすい *)
			unfold embed_listDir. exists sc. split; assumption.
		}
		pose proof (embedding_two_dir Plus Minus ls2 Hls2) as [seg1 [seg2 HPM]]; subst.
		pose proof (embedding_PM_to_PPMM_in_rect _ _ Hls2) 
			as [seg1' [seg2' [seg3' [seg4' [HPPMM [Hin_rect [Hinit_term Hslope]]]]]]].
		(* 欲しかった埋め込み *) 
		exists (ls1 ++ [seg1'; seg2'; seg3'; seg4'] ++ ls3). 
		unfold admissible. 
		split.
		+ (* 埋め込みになっていること *) 
			apply (embbeding_inner_change sc sc' l [Plus; Minus] [Plus; Plus; Minus; Minus] r ls1 [seg1; seg2] [seg1'; seg2'; seg3'; seg4'] ls3); 
				try assumption; try discriminate.
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_head_tail. destruct l; discriminate.
			* symmetry. assumption.
		+ (* その埋め込みが開であること *) 
			apply (seg_in_rectangle_keep_openness _ _ [seg1; seg2] _ ); try assumption; try congruence.
			* apply oneway_then_open. apply (embedding_oneway_listDir [Plus; Plus; Minus; Minus]); try assumption.
				apply PPMM_is_oneway.
Qed.

Lemma AdmissibleDirs_r2_Minus_inv: forall l r,
  AdmissibleDirs (l ++ [Minus; Plus] ++ r) -> AdmissibleDirs (l ++ [Minus; Minus; Plus; Plus] ++ r).
Proof.
Admitted.

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