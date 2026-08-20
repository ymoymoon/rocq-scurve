Require Import Admissible.
Require Import Reduction.
Require Import Stdlib.Reals.Reals.
Require Import Embed.
Require Import PrimitiveSegment.
Require Import Segment.
Require Import ListExt.
Require Import Sparse.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.


(* --------------------------------------------------------------------------- *)
(* extend に関する補題．extend / segment_border 本体の定義と公理は Segment.v 参照 *)

(* 引数のリスト ls を extend した時に， ls の n 番目のセグメントの上を指すのは
		nth (segment_border ls) <= t <= (n+1)th (segment_border ls)
		また segment_border ls の先頭要素より小さい t では先頭の延長線上を指し，
		segment_border ls の最後の要素より大きい t では末尾の延長線上を指す *)
Lemma extention_split : forall t ls,
	let p := extend ls t in
	ls <> []
	-> (exists border0 t', (* 先頭の延長線上 *)
			nth_error (segment_border ls) 0 = Some border0 /\
			t <= border0 /\ t' <= 0 /\ p = point (hd_segment ls) t')
	\/ (exists n border1 border2 t' seg, (* セグメント上 *)
			nth_error ls n = Some seg /\
			nth_error (segment_border ls) n = Some border1 /\
			nth_error (segment_border ls) (S n) = Some border2 /\
			border1 < t <= border2 /\ 0 < t' <= 1 /\ p = point seg t')
	\/ (exists border_last t', (* 末尾の延長線上 *)
			nth_error (segment_border ls) (length ls) = Some border_last /\
			border_last < t /\ 1 < t' /\ p = point (last_segment ls) t').
Proof.
	intros t ls p Hne.
	destruct (extend_pick_spec ls t Hne) as [n [s [bn [bn1 [Hs [Hbn [Hbn1 [Hcase Heq]]]]]]]].
	assert (Hp: p = point s ((t - bn) / (bn1 - bn))).
	{ unfold p, extend. rewrite Heq. reflexivity. }
	assert (Hlt: bn < bn1) by (eapply border_increasing; eauto).
	destruct Hcase as [[Hn0 Ht] | [Hmid | [Hlast Ht]]].
	- (* 先頭の延長線上 *) left. subst n.
		exists bn, ((t - bn) / (bn1 - bn)).
		split; [exact Hbn |].
		split; [exact Ht |].
		split.
		+ apply (proj2 (affine_param_iff_le bn bn1 t 0 Hlt)). lra.
		+ rewrite Hp. unfold hd_segment.
			pose proof (nth_error_hd default_segment ls Hs) as Hhd.
			rewrite Hhd. reflexivity.
	- (* セグメント上 *) right; left.
		exists n, bn, bn1, ((t - bn) / (bn1 - bn)), s.
		split; [exact Hs |].
		split; [exact Hbn |].
		split; [exact Hbn1 |].
		split; [lra |].
		split; [split |].
		+ apply (proj2 (affine_param_iff_gt bn bn1 t 0 Hlt)). lra.
		+ apply (proj2 (affine_param_iff_le bn bn1 t 1 Hlt)). lra.
		+ exact Hp.
	- (* 末尾の延長線上 *) right; right.
		assert (Hlen: (length ls - 1)%nat = n) by lia.
		assert (Hs': nth_error ls (length ls - 1)%nat = Some s) by (rewrite Hlen; exact Hs).
		pose proof (nth_error_last default_segment Hne) as Hlast_eq.
		rewrite Hs' in Hlast_eq.
		assert (Hbn1' : nth_error (segment_border ls) (length ls) = Some bn1) by (rewrite <- Hlast, Hbn1; reflexivity).
		exists bn1, ((t - bn) / (bn1 - bn)).
		split; [exact Hbn1' |].
		split; [exact Ht |].
		split.
		+ apply (proj2 (affine_param_iff_gt bn bn1 t 1 Hlt)). lra.
		+ rewrite Hp. unfold last_segment. congruence.
Qed.

(* extend した延長部分の先頭だけで交差は起こらない *)
Lemma extend_head_not_cross : forall ls t1 t2 border_first,
	ls <> []
	-> nth_error (segment_border ls) 0 = Some border_first
	-> t1 <= border_first
	-> t2 <= border_first
	-> extend ls t1 = extend ls t2
	-> t1 = t2.
Proof.
	intros ls t1 t2 b0 Hne Hb0 Ht1 Ht2 Hext.
	destruct (extend_pick_spec ls t1 Hne) as [n1 [s1 [bn1a [bn1b [Hs1 [Hbn1a [Hbn1b [Hcase1 Heq1]]]]]]]].
	destruct (extend_pick_spec ls t2 Hne) as [n2 [s2 [bn2a [bn2b [Hs2 [Hbn2a [Hbn2b [Hcase2 Heq2]]]]]]]].
	assert (Hn1: n1 = O).
	{ destruct n1 as [|n1']; [reflexivity | exfalso].
		assert (Hb0lt: b0 < bn1a).
		{ apply (Increasing_lt (segment_border ls) O (S n1') b0 bn1a (segment_border_increasing ls));
				[lia | exact Hb0 | exact Hbn1a]. }
		destruct Hcase1 as [[Hz _] | [Hmid | [Hlast Ht]]]; [discriminate Hz | lra |].
		assert (Hlt1: bn1a < bn1b) by (eapply border_increasing; eauto). lra. }
	assert (Hn2: n2 = O).
	{ destruct n2 as [|n2']; [reflexivity | exfalso].
		assert (Hb0lt: b0 < bn2a).
		{ apply (Increasing_lt (segment_border ls) O (S n2') b0 bn2a (segment_border_increasing ls));
				[lia | exact Hb0 | exact Hbn2a]. }
		destruct Hcase2 as [[Hz _] | [Hmid | [Hlast Ht]]]; [discriminate Hz | lra |].
		assert (Hlt2: bn2a < bn2b) by (eapply border_increasing; eauto). lra. }
	subst n1 n2.
	rewrite Hb0 in Hbn1a, Hbn2a.
	injection Hbn1a as Hbn1a. injection Hbn2a as Hbn2a. subst bn1a bn2a.
	assert (Hbb: bn1b = bn2b) by congruence. subst bn2b.
	assert (Hs: s1 = s2) by congruence. subst s2.
	assert (Hlt: b0 < bn1b) by (eapply border_increasing; eauto).
	assert (Hp1: extend ls t1 = point s1 ((t1 - b0) / (bn1b - b0))) by (unfold extend; rewrite Heq1; reflexivity).
	assert (Hp2: extend ls t2 = point s1 ((t2 - b0) / (bn1b - b0))) by (unfold extend; rewrite Heq2; reflexivity).
	rewrite Hp1, Hp2 in Hext.
	assert (Haff: (t1 - b0) / (bn1b - b0) = (t2 - b0) / (bn1b - b0)) by (eapply point_injective; eauto).
	eapply affine_inj; eauto.
Qed.

(* extend した延長部分の末尾だけで交差は起こらない *)
Lemma extend_last_not_cross : forall ls t1 t2 border_last,
	ls <> []
	-> nth_error (segment_border ls) (length ls) = Some border_last
	-> border_last < t1
	-> border_last < t2
	-> extend ls t1 = extend ls t2
	-> t1 = t2.
Proof.
	intros ls t1 t2 blast Hne Hblast Ht1 Ht2 Hext.
	destruct (extend_pick_spec ls t1 Hne) as [n1 [s1 [bn1a [bn1b [Hs1 [Hbn1a [Hbn1b [Hcase1 Heq1]]]]]]]].
	destruct (extend_pick_spec ls t2 Hne) as [n2 [s2 [bn2a [bn2b [Hs2 [Hbn2a [Hbn2b [Hcase2 Heq2]]]]]]]].
	assert (Hn1lt: (n1 < length ls)%nat) by (apply nth_error_Some; rewrite Hs1; discriminate).
	assert (Hn2lt: (n2 < length ls)%nat) by (apply nth_error_Some; rewrite Hs2; discriminate).
	assert (Hn1: S n1 = length ls).
	{ destruct (Nat.eq_dec (S n1) (length ls)) as [Heqn|Hneqn]; [exact Heqn | exfalso].
		assert (Hb: bn1b < blast).
		{ apply (Increasing_lt (segment_border ls) (S n1) (length ls) bn1b blast (segment_border_increasing ls));
				[lia | exact Hbn1b | exact Hblast]. }
		destruct Hcase1 as [[Hz Ht] | [Hmid | [Hlast Ht]]].
		- assert (Hlt1: bn1a < bn1b) by (eapply border_increasing; eauto). lra.
		- lra.
		- lia. }
	assert (Hn2: S n2 = length ls).
	{ destruct (Nat.eq_dec (S n2) (length ls)) as [Heqn|Hneqn]; [exact Heqn | exfalso].
		assert (Hb: bn2b < blast).
		{ apply (Increasing_lt (segment_border ls) (S n2) (length ls) bn2b blast (segment_border_increasing ls));
				[lia | exact Hbn2b | exact Hblast]. }
		destruct Hcase2 as [[Hz Ht] | [Hmid | [Hlast Ht]]].
		- assert (Hlt2: bn2a < bn2b) by (eapply border_increasing; eauto). lra.
		- lra.
		- lia. }
	assert (Hn1n2: n1 = n2) by lia. subst n2.
	assert (Hbn1b_alt: nth_error (segment_border ls) (S n1) = Some blast) by (rewrite Hn1; exact Hblast).
	assert (Ebb1: bn1b = blast) by congruence.
	assert (Ebb2: bn2b = blast) by congruence.
	subst bn1b bn2b.
	assert (Hbb: bn1a = bn2a) by congruence. subst bn2a.
	assert (Hs: s1 = s2) by congruence. subst s2.
	assert (Hlt: bn1a < blast) by (eapply border_increasing; eauto).
	assert (Hp1: extend ls t1 = point s1 ((t1 - bn1a) / (blast - bn1a))) by (unfold extend; rewrite Heq1; reflexivity).
	assert (Hp2: extend ls t2 = point s1 ((t2 - bn1a) / (blast - bn1a))) by (unfold extend; rewrite Heq2; reflexivity).
	rewrite Hp1, Hp2 in Hext.
	assert (Haff: (t1 - bn1a) / (blast - bn1a) = (t2 - bn1a) / (blast - bn1a)) by (eapply point_injective; eauto).
	eapply affine_inj; eauto.
Qed.

(* extend した時も１つのセグメントの中で交差は起こらない *)
(* TODO : extend しない時の定理とまとめられないか *)
Lemma extend_one_seg_not_cross : forall ls n t1 t2 border1 border2,
	nth_error (segment_border ls) n = Some border1
	-> nth_error (segment_border ls) (S n) = Some border2
	-> border1 < t1 <= border2
	-> border1 < t2 <= border2
	-> extend ls t1 = extend ls t2
	-> t1 = t2.
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
			t1' <= 0 /\ 0 < t2' <= 1 /\ In seg ls /\
				p1 = point (hd_segment ls) t1' /\ p2 = point seg t2')
	\/ (exists t1' t2', (* t1 は先頭の延長線上， t2 は末尾の延長線上 *)
			t1' <= 0 /\ 1 < t2' /\ 
				p1 = point (hd_segment ls) t1' /\ p2 = point (last_segment ls) t2')
	\/ (exists t1' t2' seg, (* t1 はセグメント上， t2 は先頭の延長線上 *)
			0 < t1' <= 1 /\ t2' <= 0 /\ In seg ls /\
				p1 = point seg t1' /\ p2 = point (hd_segment ls) t2')
	\/ (exists t1' t2' seg, (* t1, t2 とも同じセグメント上 *)
			0 < t1' <= 1 /\ 0 < t2' <= 1 /\ t1' <> t2' /\ In seg ls /\
				p1 = point seg t1' /\ p2 = point seg t2')
	\/ (exists t1' t2' seg1 seg2, (* t1, t2 が異なるセグメント上 (t1 < t2) *)
			0 < t1' <= 1 /\ 0 < t2' <= 1 /\ In_order seg1 seg2 ls /\
				p1 = point seg1 t1' /\ p2 = point seg2 t2')
	\/ (exists t1' t2' seg1 seg2, (* t1, t2 が異なるセグメント上 (t1 > t2) *)
			0 < t1' <= 1 /\ 0 < t2' <= 1 /\ In_order seg2 seg1 ls /\
				p1 = point seg1 t1' /\ p2 = point seg2 t2')
	\/ (exists t1' t2' seg, (* t1 はセグメント上， t2 は末尾の延長線上 *)
			0 < t1' <= 1 /\ 1 < t2' /\ In seg ls /\
				p1 = point seg t1' /\ p2 = point (last_segment ls) t2')
	\/ (exists t1' t2', (* t1 は末尾の延長線上， t2 は先頭の延長線上 *)
			1 < t1' /\ t2' <= 0 /\ 
				p1 = point (last_segment ls) t1' /\ p2 = point (hd_segment ls) t2')
	\/ (exists t1' t2' seg, (* t1 は末尾の延長線上， t2 はセグメント上 *)
			1 < t1' /\ 0 < t2' <= 1 /\ In seg ls /\
				p1 = point (last_segment ls) t1' /\ p2 = point seg t2')
	\/ (exists t1' t2', (* t1, t2 とも末尾の延長線上 *)
			1 < t1' /\ 1 < t2' /\ t1' <> t2' /\
				p1 = point (last_segment ls) t1' /\ p2 = point (last_segment ls) t2').
Proof. 
	intros t1 t2 ls p1 p2 Hls H12.
	pose proof (extention_split t1 ls Hls) as H1.
	pose proof (extention_split t2 ls Hls) as H2.
	destruct H1 as [[border_first1 [t1' [Hnth1 [Ht1 [Ht1' Heq1]]]]] | [[n1 [border11 [border12 [t1' [seg1 [Hnth1 [Hnth11 [Hnth12 [Ht1 [Ht1' Heq1]]]]]]]]]] | [border_last1 [t1' [Hnth1 [Ht1 [Ht1' Heq1]]]]]]];
	destruct H2 as [[border_first2 [t2' [Hnth2 [Ht2 [Ht2' Heq2]]]]] | [[n2 [border21 [border22 [t2' [seg2 [Hnth2 [Hnth21 [Hnth22 [Ht2 [Ht2' Heq2]]]]]]]]]] | [border_last2 [t2' [Hnth2 [Ht2 [Ht2' Heq2]]]]]]].
	- (* t1, t2 とも先頭の延長線上 *) left. 
		exists t1', t2'. repeat split; try tauto.
		assert (border_first1 = border_first2) by congruence.
		subst.
		intros contra; subst.
		apply H12.
		eapply extend_head_not_cross; try eassumption. 
		congruence.
	- (* t1 は先頭の延長線上， t2 はセグメント上 *) right; left. 
		exists t1', t2', seg2. 
		apply nth_error_In in Hnth2. tauto.
	- (* t1 は先頭の延長線上， t2 は末尾の延長線上 *) do 2 right; left.
		exists t1', t2'. tauto.
	- (* t1 はセグメント上， t2 は先頭の延長線上 *) do 3 right; left.
		exists t1', t2', seg1.
		apply nth_error_In in Hnth1. tauto.
	- (* t1, t2 ともセグメント上 *)
		destruct (Nat.eqb n1 n2) eqn: E.
		+ (* t1, t2 とも同じセグメント上 *) do 4 right; left.
			apply Nat.eqb_eq in E.
			subst. 
			assert (seg1 = seg2) by congruence.
			assert (border11 = border21) by congruence.
			assert (border12 = border22) by congruence.
			subst.
			apply nth_error_In in Hnth1.
		  exists t1', t2', seg2. repeat split; try tauto.
			(* 補題が必要 *)
			intros contra; subst.
			apply H12.
			eapply (extend_one_seg_not_cross _ n2); try eassumption. 
		 	congruence.
		+ destruct (Nat.leb n1 n2) eqn: E1.
			* (* t1, t2 が異なるセグメント上 (t1 < t2) *) do 5 right; left.
				assert ((n1 < n2)%nat). {
					apply Nat.leb_le in E1.
					destruct E1; try (rewrite Nat.eqb_refl in E; congruence).
					lia.
				}
				exists t1', t2', seg1, seg2. 
				assert (In_order seg1 seg2 ls) by (eapply In_order_nth; eassumption). 
				tauto.
			* (* t1, t2 が異なるセグメント上 (t1 > t2) *) do 6 right; left.
				assert ((n2 < n1)%nat). {
					apply Nat.leb_gt in E1.
					assumption.
				}
				exists t1', t2', seg1, seg2. 
				assert (In_order seg2 seg1 ls) by (eapply In_order_nth; eassumption). 
				tauto.
	- (* t1 はセグメント上， t2 は末尾の延長線上 *) do 7 right; left.
		exists t1', t2', seg1. 
		apply nth_error_In in Hnth1. tauto.
	- (* t1 は末尾の延長線上， t2 は先頭の延長線上 *) do 8 right; left.
		exists t1', t2'. tauto.
	- (* t1 は末尾の延長線上， t2 はセグメント上 *) do 9 right; left.
		exists t1', t2', seg2. 
		apply nth_error_In in Hnth2. tauto.
	- (* t1, t2 とも末尾の延長線上 *) repeat right.
		exists t1', t2'. repeat split; try tauto.
		assert (border_last1 = border_last2) by congruence.
		subst.
		intros contra; subst.
		apply H12.
		eapply extend_last_not_cross; try eassumption. 
		congruence.
Qed.

(* 2つ以上離れたセグメントが１点を共有していれば，それらのセグメントを含む曲線は閉 *)
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


(* 傾きを想定しているが，埋め込みの延長線を一意に定義するものであればよい *)
Parameter slope_init : Segment -> R.
Parameter slope_term : Segment -> R.

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
Admitted.

Lemma same_term_then_same_extention_last : forall ls1 ls2,
	let seg1 := last_segment ls1 in
	let seg2 := last_segment ls2 in
	term seg1 = term seg2
	-> slope_term seg1 = slope_term seg2
	-> same_extention_last ls1 ls2.
Proof. 
Admitted.


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
(* Lemma sparse_in_rect_change : forall (ls rs sub_ls sub_ls' : list Segment), 
	sparse ls sub_ls rs
	-> (forall rr, onSegmentlist sub_ls' rr -> in_rect sub_ls rr) 
	-> same_init_and_term sub_ls sub_ls' 
	-> same_slope_init_and_term sub_ls sub_ls'
	-> sparse ls sub_ls' rs.
Proof. 
Admitted. *)


(* 0 で割ったら 0 なので注意 *)
Definition slope_two (rr1 rr2 : Point) :=
	let (x1, y1) := rr1 in
	let (x2, y2) := rr2 in (y2 - y1) / (x2 - x1).


(* embed_sparsely_listDir を強めたもの
		sub_ds の埋め込みについて，その部分の埋め込みの終点が始点の右上側にあり，
		始点での傾きが終点での傾き（どちらも正）よりも大きいようにできる *)
(* TODO：embed_sparsely_listDir に統合しても良い *)
Lemma embed_sparsely_listDir_PMP (ds1 ds2 : list Direction) :
	AdmissibleDirs (ds1 ++ [Plus; Minus; Plus] ++ ds2)
	-> exists l r seg1 seg2 seg3,
		rightabove (init seg1) (term seg3)
	  /\ 0 < slope_term seg3 < slope_init seg1 
		/\ embed_listDir ds1 l
		/\ embed_listDir [Plus; Minus; Plus] [seg1; seg2; seg3]
		/\ embed_listDir ds2 r
		/\ embed_listDir (ds1 ++ [Plus; Minus; Plus] ++ ds2) (l ++ [seg1; seg2; seg3] ++ r)
		/\ ~ close (l ++ [seg1; seg2; seg3] ++ r)
		/\ sparse l [seg1; seg2; seg3] r.
Proof. Admitted.

(* embed_sparsely_listDir_PMP の Minus 版．x 軸に関する鏡映により，
		rightabove は rightbelow に，傾きの大小・符号はすべて反転する
		（0 < slope_term seg3 < slope_init seg1 は slope_init seg1 < slope_term seg3 < 0 になる） *)
Lemma embed_sparsely_listDir_MPM (ds1 ds2 : list Direction) :
	AdmissibleDirs (ds1 ++ [Minus; Plus; Minus] ++ ds2)
	-> exists l r seg1 seg2 seg3,
		rightbelow (init seg1) (term seg3)
	  /\ slope_init seg1 < slope_term seg3 < 0
		/\ embed_listDir ds1 l
		/\ embed_listDir [Minus; Plus; Minus] [seg1; seg2; seg3]
		/\ embed_listDir ds2 r
		/\ embed_listDir (ds1 ++ [Minus; Plus; Minus] ++ ds2) (l ++ [seg1; seg2; seg3] ++ r)
		/\ ~ close (l ++ [seg1; seg2; seg3] ++ r)
		/\ sparse l [seg1; seg2; seg3] r.
Proof. Admitted.

Lemma embed_sparsely_listDir_PPMM (ds1 ds2 : list Direction) :
	AdmissibleDirs (ds1 ++ [Plus; Plus; Minus; Minus] ++ ds2)
	-> exists l r seg1 seg2 seg3 seg4, 
		rightabove (init seg1) (term seg4)
		/\ slope_two (init seg1) (term seg4) < slope_init seg1
		/\ slope_two (init seg1) (term seg4) < slope_term seg4
		/\ embed_listDir ds1 l
		/\ embed_listDir [Plus; Plus; Minus; Minus] [seg1; seg2; seg3; seg4]
		/\ embed_listDir ds2 r
		/\ embed_listDir (ds1 ++ [Plus; Plus; Minus; Minus] ++ ds2) (l ++ [seg1; seg2; seg3; seg4] ++ r)
		/\ ~ close (l ++ [seg1; seg2; seg3; seg4] ++ r)
		/\ sparse l [seg1; seg2; seg3; seg4] r.
Proof. Admitted.

(* embed_sparsely_listDir_PPMM の Minus 版．鏡映により rightabove -> rightbelow，
		slope_two（傾き）や slope_init/slope_term の大小関係もすべて符号・向きが反転する *)
Lemma embed_sparsely_listDir_MMPP (ds1 ds2 : list Direction) :
	AdmissibleDirs (ds1 ++ [Minus; Minus; Plus; Plus] ++ ds2)
	-> exists l r seg1 seg2 seg3 seg4,
		rightbelow (init seg1) (term seg4)
		/\ slope_init seg1 < slope_two (init seg1) (term seg4)
		/\ slope_term seg4 < slope_two (init seg1) (term seg4)
		/\ embed_listDir ds1 l
		/\ embed_listDir [Minus; Minus; Plus; Plus] [seg1; seg2; seg3; seg4]
		/\ embed_listDir ds2 r
		/\ embed_listDir (ds1 ++ [Minus; Minus; Plus; Plus] ++ ds2) (l ++ [seg1; seg2; seg3; seg4] ++ r)
		/\ ~ close (l ++ [seg1; seg2; seg3; seg4] ++ r)
		/\ sparse l [seg1; seg2; seg3; seg4] r.
Proof. Admitted.

(* Plus (の向きを持つ Primitive Segment) の埋め込みを，端点とそこでの傾きを保存したまま
		[Plus; Minus; Plus] の埋め込みとなる３つに矩形内で分割できる *)
Lemma embedding_P_to_PMP_in_rect : forall (seg : Segment),
	embed_listDir [Plus] [seg]
	-> exists seg1 seg2 seg3,
		embed_listDir [Plus; Minus; Plus] [seg1; seg2; seg3] (* この内部で seg1-3 が連結していることは示されてほしい *)
		/\ (forall rr, onSegmentlist [seg1; seg2; seg3] rr
				-> in_rect (rect_of [seg]) rr) (* seg が張る矩形の内部で分割できている *)
		/\ same_init_and_term [seg] [seg1; seg2; seg3]
		/\ same_slope_init_and_term [seg] [seg1; seg2; seg3].
Proof. 
	(* seg1, seg3 は十分小さくとり， seg1 の終点の傾きは 0 に， seg3 の始点の傾きは
		無限大あるいは十分大きくとる．その後端点を結ぶように seg2 をとる．
		具体的には，seg3 の始点が seg1 の終点より右上にあり，
		seg3 の始点での傾きが seg1 の終点での傾きより大きくなるようにすれば良い． *)
Admitted.

(* embedding_P_to_PMP_in_rect の Minus 版 *)
Lemma embedding_M_to_MPM_in_rect : forall (seg : Segment),
	embed_listDir [Minus] [seg]
	-> exists seg1 seg2 seg3,
		embed_listDir [Minus; Plus; Minus] [seg1; seg2; seg3]
		/\ (forall rr, onSegmentlist [seg1; seg2; seg3] rr
				-> in_rect (rect_of [seg]) rr)
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
				-> in_rect (rect_of [seg1; seg2]) rr) (* seg が張る矩形の内部で分割できている *)
		/\ same_init_and_term [seg1; seg2] [seg1'; seg2'; seg3'; seg4']
		/\ same_slope_init_and_term [seg1; seg2] [seg1'; seg2'; seg3'; seg4'].
Proof. Admitted.

(* embedding_PM_to_PPMM_in_rect の Minus 版 *)
Lemma embedding_MP_to_MMPP_in_rect : forall (seg1 seg2 : Segment),
	embed_listDir [Minus; Plus] [seg1; seg2]
	-> exists seg1' seg2' seg3' seg4',
		embed_listDir [Minus; Minus; Plus; Plus] [seg1'; seg2'; seg3'; seg4']
		/\ (forall rr, onSegmentlist [seg1'; seg2'; seg3'; seg4'] rr
				-> in_rect (rect_of [seg1; seg2]) rr)
		/\ same_init_and_term [seg1; seg2] [seg1'; seg2'; seg3'; seg4']
		/\ same_slope_init_and_term [seg1; seg2] [seg1'; seg2'; seg3'; seg4'].
Proof. Admitted.

(* [Plus; Minus; Plus] の埋め込みは，その部分の埋め込みの終点が始点の右上側にあり，
		始点での傾きが終点での傾き（どちらも正）よりも大きいならば，
	  端点とそこでの傾きを保存したまま，矩形内で
		Plus の埋め込みに変更できる *)
(* TODO : もう少し一般化しても良いかもしれない *)
Lemma embedding_PMP_to_P_in_rect : forall (seg1 seg2 seg3 : Segment),
	rightabove (init seg1) (term seg3)
	-> 0 < slope_term seg3 < slope_init seg1
	-> embed_listDir [Plus; Minus; Plus] [seg1; seg2; seg3]
	->
	exists seg,
		embed_listDir [Plus] [seg]
		/\ (forall rr, onSegment seg rr
				-> in_rect (rect_of [seg1; seg2; seg3]) rr ) (* seg が張る矩形の内部で分割できている *)
		/\ same_init_and_term [seg1; seg2; seg3] [seg]
		/\ same_slope_init_and_term [seg1; seg2; seg3] [seg].
Proof.
	(* 始点・終点・それぞれでの傾きが固定されているので，具体的に Plus の埋め込みが取れるはず *)
Admitted.

(* embedding_PMP_to_P_in_rect の Minus 版 *)
Lemma embedding_MPM_to_M_in_rect : forall (seg1 seg2 seg3 : Segment),
	rightbelow (init seg1) (term seg3)
	-> slope_init seg1 < slope_term seg3 < 0
	-> embed_listDir [Minus; Plus; Minus] [seg1; seg2; seg3]
	->
	exists seg,
		embed_listDir [Minus] [seg]
		/\ (forall rr, onSegment seg rr
				-> in_rect (rect_of [seg1; seg2; seg3]) rr )
		/\ same_init_and_term [seg1; seg2; seg3] [seg]
		/\ same_slope_init_and_term [seg1; seg2; seg3] [seg].
Proof. Admitted.

(* [Plus; Plus; Minus; Minus] の埋め込みは，その部分の埋め込みの終点が始点の右上側にあり，
		始点・終点での傾きがどちらも十分大きいならば，
		端点とそこでの傾きを保存したまま，矩形内で
		[Plus; Minus] の埋め込みに変更できる *)
Lemma embedding_PPMM_to_PM_in_rect : forall (seg1 seg2 seg3 seg4 : Segment),
	rightabove (init seg1) (term seg4)
	-> slope_two (init seg1) (term seg4) < slope_init seg1
	-> slope_two (init seg1) (term seg4) < slope_term seg4
	-> embed_listDir [Plus; Plus; Minus; Minus] [seg1; seg2; seg3; seg4]
	->
	exists seg1' seg2',
		embed_listDir [Plus; Minus] [seg1'; seg2'] 
		/\ (forall rr, onSegmentlist [seg1'; seg2'] rr
				-> in_rect (rect_of [seg1; seg2; seg3; seg4]) rr) (* seg が張る矩形の内部で分割できている *)
		/\ same_init_and_term [seg1; seg2; seg3; seg4] [seg1'; seg2']
		/\ same_slope_init_and_term [seg1; seg2; seg3; seg4] [seg1'; seg2'].
Proof.
	(* 始点から中心へ，終点から中心へそれぞれ Plus, Minus の埋め込みをとり，繋げれば良さそう *)
Admitted.

(* embedding_PPMM_to_PM_in_rect の Minus 版 *)
Lemma embedding_MMPP_to_MP_in_rect : forall (seg1 seg2 seg3 seg4 : Segment),
	rightbelow (init seg1) (term seg4)
	-> slope_init seg1 < slope_two (init seg1) (term seg4)
	-> slope_term seg4 < slope_two (init seg1) (term seg4)
	-> embed_listDir [Minus; Minus; Plus; Plus] [seg1; seg2; seg3; seg4]
	->
	exists seg1' seg2',
		embed_listDir [Minus; Plus] [seg1'; seg2']
		/\ (forall rr, onSegmentlist [seg1'; seg2'] rr
				-> in_rect (rect_of [seg1; seg2; seg3; seg4]) rr)
		/\ same_init_and_term [seg1; seg2; seg3; seg4] [seg1'; seg2']
		/\ same_slope_init_and_term [seg1; seg2; seg3; seg4] [seg1'; seg2'].
Proof. Admitted.

(*  向き ds1 ++ ds2 ++ ds3 の ds2 (の向きを持つ scurve) の埋め込みを，端点の条件を満たしつつ
		ds2' の埋め込みに変えたら，向き ds1 ++ ds2' ++ ds3 の埋め込みである *)
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
Proof. 
	intros sc1 sc2 ds1 ds2 ds2' ds3 ls1 ls2 ls2' ls3.
	intros Hls2 Hls2' Hembed Hembed_dir1 Hembed_dir2 Hinit_term Hdir1 Hdir2 Hhead.
Admitted.

(* 【証明の本質としている補題２】 sub_ls の周りが疎な開埋め込みにおいて，端点で傾きを保ちつつ
		sub_ls をその領域に収まる開な sub_ls' に置き換えても開のまま *)
(* TODO : もうちょっと自動化できるはず．．． *)
Lemma seg_in_rectangle_keep_openness : forall (ls rs sub_ls sub_ls' : list Segment),
	sub_ls <> []
	-> sub_ls' <> [] 
	-> ~ close sub_ls'
	-> ~ close (ls ++ sub_ls ++ rs)
	-> sparse ls sub_ls rs
	-> (forall rr, onSegmentlist sub_ls' rr -> in_rect (rect_of sub_ls) rr) 
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
			repeat rewrite <- last_app; try reflexivity; discriminate.
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
		(* 似ている場合分けばかりなので，まとめて処理したい *)

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
				eapply (head_seg_cross_close intersection seg post _); auto. 
				-- exists t1'. split; subst post intersection; congruence. 
				-- exists t2'. split; subst post intersection; try lra; congruence.
				-- admit. 
			+ (* 先頭の延長線と sub_ls' が交わっている場合： pre が疎であることに矛盾 *) 
				assert (Hin_rect_yes : in_rect (rect_of sub_ls) intersection). {
					apply Hin_rect. exists seg. split; auto.
					exists t2'. split; subst post intersection; try lra; congruence. 
				}
				assert (Hin_rect_no : ~ in_rect (rect_of sub_ls) intersection). {
					apply Hsparse.
					left.
					apply Hsame_ex_head. 
					exists t1'. split; subst post intersection; congruence. 
				} 
				auto.

		- (* t1 が先頭の延長線上の点を， t2 が末尾の延長線上の点を指す場合： pre が開であることに矛盾 *)
			apply Hopen. 
			apply (head_last_cross_close intersection post); auto.
			* intros contra. apply app_eq_nil in contra.
				destruct contra as [_ contra].
				apply app_eq_nil in contra.
				destruct contra as [contra _]. contradiction.
			* exists t1'. split; subst post intersection; congruence. 
			* exists t2'. split; subst post intersection; try lra; congruence. 

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
				eapply (head_seg_cross_close intersection seg post _); auto. 
				-- exists t2'. split; subst post intersection; congruence. 
				-- exists t1'. split; subst post intersection; try lra; congruence. 
				-- admit.
			+ (* 先頭の延長線と sub_ls' が交わっている場合： pre が疎であることに矛盾 *) 
				assert (Hin_rect_yes : in_rect (rect_of sub_ls) intersection). {
					apply Hin_rect. exists seg. split; auto.
					exists t1'. split; subst post intersection; try lra; congruence. 
				}
				assert (Hin_rect_no : ~ in_rect (rect_of sub_ls) intersection). {
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
				-- admit. 
				-- exists t1'. split; subst post intersection; try lra; congruence. 
				-- exists t2'. split; subst post intersection; try lra; congruence. 
				-- admit.
			+ (* １つが pre 上の点，もう１つが sub_ls' 上の点の場合１： pre が疎であることに矛盾 *) 
				assert (Hin_rect_yes : in_rect (rect_of sub_ls) intersection). {
					destruct Hin.
					apply Hin_rect. exists seg1. split; auto.
					exists t1'. split; subst post intersection; try lra; congruence. 
				}
				assert (Hin_rect_no : ~ in_rect (rect_of sub_ls) intersection). {
					destruct Hin.
					apply Hsparse.
					right. left.
					exists seg2. split.
					* apply in_or_app. auto.
					* exists t2'. split; auto; subst post intersection; try lra; congruence. 
				} 
				auto.
			+ (* １つが pre 上の点，もう１つが sub_ls' 上の点の場合２： pre が疎であることに矛盾 *) 
				assert (Hin_rect_yes : in_rect (rect_of sub_ls) intersection). {
					destruct Hin.
					apply Hin_rect. exists seg2. split; auto.
					exists t2'. split; subst post intersection; try lra; congruence. 
				}
				assert (Hin_rect_no : ~ in_rect (rect_of sub_ls) intersection). {
					destruct Hin.
					apply Hsparse.
					right. left.
					exists seg1. split.
					* apply in_or_app. auto.
					* exists t1'. split; auto.
					lra.
				} 
				auto.
			+ (* 両方 pre 上の点である場合： pre が開であることに矛盾 *) 
				apply Hopen.
				apply (two_segs_have_same_point_close seg1 seg2 intersection). 
				-- admit.
				-- exists t1'. split; subst post intersection; try lra; congruence. 
				-- exists t2'. split; subst post intersection; try lra; congruence. 
				-- admit.

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
				-- admit.
				-- exists t2'. split; subst post intersection; try lra; congruence. 
				-- exists t1'. split; subst post intersection; try lra; congruence. 
				-- admit.
			+ (* １つが pre 上の点，もう１つが sub_ls' 上の点の場合１： pre が疎であることに矛盾 *) 
				assert (Hin_rect_yes : in_rect (rect_of sub_ls) intersection). {
					destruct Hin.
					apply Hin_rect. exists seg2. split; auto.
					exists t2'. split; subst post intersection; try lra; congruence. 
				}
				assert (Hin_rect_no : ~ in_rect (rect_of sub_ls) intersection). {
					destruct Hin.
					apply Hsparse.
					right. left.
					exists seg1. split.
					* apply in_or_app. auto.
					* exists t1'. split; auto. 
					lra.
				} 
				auto.
			+ (* １つが pre 上の点，もう１つが sub_ls' 上の点の場合２： pre が疎であることに矛盾 *) 
				assert (Hin_rect_yes : in_rect (rect_of sub_ls) intersection). {
					destruct Hin.
					apply Hin_rect. exists seg1. split; auto.
					exists t1'. split; subst post intersection; try lra; congruence. 
				}
				assert (Hin_rect_no : ~ in_rect (rect_of sub_ls) intersection). {
					destruct Hin.
					apply Hsparse.
					right. left.
					exists seg2. split.
					* apply in_or_app. auto.
					* exists t2'. split; auto; subst post intersection; try lra; congruence.
				} 
				auto.
			+ (* 両方 pre 上の点である場合： pre が開であることに矛盾 *) 
				apply Hopen.
				apply (two_segs_have_same_point_close seg2 seg1 intersection). 
				-- admit.
				-- exists t2'. split; subst post intersection; try lra; congruence. 
				-- exists t1'. split; subst post intersection; try lra; congruence. 
				-- admit.

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
				eapply (last_seg_cross_close intersection seg post _); auto. 
				-- exists t2'. split; subst post intersection; congruence. 
				-- exists t1'. split; subst post intersection; try lra; congruence. 
				-- admit.
				-- admit.
			* (* 末尾の延長線と sub_ls' が交わっている場合： pre が疎であることに矛盾 *) 
				assert (Hin_rect_yes : in_rect (rect_of sub_ls) intersection). {
					apply Hin_rect. exists seg. split; auto.
					exists t1'. split; subst post intersection; try lra; congruence. 
				}
				assert (Hin_rect_no : ~ in_rect (rect_of sub_ls) intersection). {
					apply Hsparse.
					repeat right.
					apply Hsame_ex_last. 
					exists t2'. split; subst post intersection; try lra; congruence. 
				} 
				auto.

		- (* t1 が末尾の延長線上の点を， t2 が先頭の延長線上の点を指す場合： pre が開であることに矛盾 *)
			apply Hopen. 
			apply (head_last_cross_close intersection post); auto.
			* intros contra. apply app_eq_nil in contra.
				destruct contra as [_ contra].
				apply app_eq_nil in contra.
				destruct contra as [contra _]. contradiction.
			* exists t2'. split; subst post intersection; congruence. 
			* exists t1'. split; subst post intersection; try lra; congruence. 

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
				eapply (last_seg_cross_close intersection seg post _); auto. 
				-- exists t1'. split; subst post intersection; try lra; congruence. 
				-- exists t2'. split; subst post intersection; try lra; congruence. 
				-- admit.
				-- admit.
			* (* 末尾の延長線と sub_ls' が交わっている場合： pre が疎であることに矛盾 *) 
				assert (Hin_rect_yes : in_rect (rect_of sub_ls) intersection). {
					apply Hin_rect. exists seg. split; auto.
					exists t2'. split; subst post intersection; try lra; congruence. 
				}
				assert (Hin_rect_no : ~ in_rect (rect_of sub_ls) intersection). {
					apply Hsparse.
					repeat right.
					apply Hsame_ex_last. 
					exists t1'. split; subst post intersection; try lra; congruence. 
				} 
				auto.

		- (* t1, t2 ともに末尾の延長線上の点を指す場合：矛盾 *) 
			apply H12'.
			apply (one_seg_not_cross _ _ (last_segment post)). subst post; congruence.
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
	destruct H as [ls1 [ls3 [seg1 [seg2 [seg3 [Hrightabove [Hslope [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [Hopen Hsparse]]]]]]]]]]]];
	try lra; simpl in *.
	assert (Hdir: hd Plus (l ++ Plus :: r) = orn (hd_scurve sc)). {
		unfold hd_scurve. unfold scurve_to_direction in Hdir_sc.
		destruct l; simpl in *;
		symmetry; eapply list_map_hd; apply Hdir_sc.
	}
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Plus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Plus; Minus; Plus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
	- (* 許容可能であること *)
		pose proof (embedding_PMP_to_P_in_rect seg1 seg2 seg3 Hrightabove Hslope Hls2) as [segP [HP [Hin_rect [Hinit_term Hsame_slope]]]].
		(* 欲しかった埋め込み *) 
		exists (ls1 ++ [segP] ++ ls3). 
		unfold admissible. 
		split.
		+ (* 埋め込みになっていること *) 
			apply (embbeding_inner_change sc sc' l [Plus; Minus; Plus] [Plus] r ls1 [seg1; seg2; seg3] [segP] ls3); 
				try assumption; try discriminate.
			(* 仮定を満たすことはほぼ作業的に示せる *)
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
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
	intros l r admds.
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely_listDir_MPM _ _ admds) as H.
	destruct H as [ls1 [ls3 [seg1 [seg2 [seg3 [Hrightbelow [Hslope [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [Hopen Hsparse]]]]]]]]]]]];
	try lra; simpl in *.
	assert (Hdir: hd Minus (l ++ Minus :: r) = orn (hd_scurve sc)). {
		unfold hd_scurve. unfold scurve_to_direction in Hdir_sc.
		destruct l; simpl in *;
		symmetry; eapply list_map_hd; apply Hdir_sc.
	}
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Minus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Minus; Plus; Minus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
	- (* 許容可能であること *)
		pose proof (embedding_MPM_to_M_in_rect seg1 seg2 seg3 Hrightbelow Hslope Hls2) as [segM [HM [Hin_rect [Hinit_term Hsame_slope]]]].
		(* 欲しかった埋め込み *)
		exists (ls1 ++ [segM] ++ ls3).
		unfold admissible.
		split.
		+ (* 埋め込みになっていること *)
			apply (embbeding_inner_change sc sc' l [Minus; Plus; Minus] [Minus] r ls1 [seg1; seg2; seg3] [segM] ls3);
				try assumption; try discriminate.
			(* 仮定を満たすことはほぼ作業的に示せる *)
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
			* symmetry. assumption.
		+ (* その埋め込みが開であること *)
			apply (seg_in_rectangle_keep_openness _ _ [seg1; seg2; seg3] [segM]);
				try assumption; try (symmetry; assumption); try congruence.
			(* 残った subgoal もほぼ自明 *)
			* apply oneway_then_open. apply (embedding_oneway_listDir [Minus]); try assumption.
				apply M_is_oneway.
			* intros rr [seg' [H1 H2]]. apply Hin_rect.
				destruct H1; [subst; assumption | exfalso; assumption].
Qed.

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
		symmetry; eapply list_map_hd; apply Hdir_sc.
	}	
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Plus :: Minus :: Plus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Plus; Minus; Plus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
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
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
			* symmetry. assumption.
		+ (* その埋め込みが開であること *) 
			apply (seg_in_rectangle_keep_openness _ _ [segP] _ ); try assumption; try congruence.
			* apply oneway_then_open. apply (embedding_oneway_listDir [Plus; Minus; Plus]); try assumption.
				apply PMP_is_oneway.
Qed.

Lemma AdmissibleDirs_r1_Minus_inv: forall l r,
  AdmissibleDirs (l ++ [Minus] ++ r) -> AdmissibleDirs (l ++ [Minus; Plus; Minus] ++ r).
Proof.
	intros l r admds.
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely_listDir _ _ _ admds M_is_oneway)
		as [ls1 [ls3 [ls2 [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [Hopen Hsparse]]]]]]]];
	simpl in *.
	assert (Hdir: hd Minus (l ++ Minus :: Plus :: Minus :: r) = orn (hd_scurve sc)). {
		unfold hd_scurve. unfold scurve_to_direction in Hdir_sc.
		destruct l; simpl in *;
		symmetry; eapply list_map_hd; apply Hdir_sc.
	}
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Minus :: Plus :: Minus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Minus; Plus; Minus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
	- (* 許容可能であること *)
		assert (H: embed_listDir (l ++ [Minus] ++ r) (ls1 ++ ls2 ++ ls3)). { (* scurve ではなく向き列の方が扱いやすい *)
			unfold embed_listDir. exists sc. split; assumption.
		}
		pose proof (embedding_one_dir Minus ls2 Hls2) as [segM HM]; subst.
		pose proof (embedding_M_to_MPM_in_rect segM Hls2)
			as [seg1 [seg2 [seg3 [HMPM [Hin_rect [Hinit_term Hslope]]]]]].
		(* 欲しかった埋め込み *)
		exists (ls1 ++ [seg1; seg2; seg3] ++ ls3).
		unfold admissible.
		split.
		+ (* 埋め込みになっていること *)
			apply (embbeding_inner_change sc sc' l [Minus] [Minus; Plus; Minus] r ls1 [segM] [seg1; seg2; seg3] ls3);
				try assumption; try discriminate.
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
			* symmetry. assumption.
		+ (* その埋め込みが開であること *)
			apply (seg_in_rectangle_keep_openness _ _ [segM] _ ); try assumption; try congruence.
			* apply oneway_then_open. apply (embedding_oneway_listDir [Minus; Plus; Minus]); try assumption.
				apply MPM_is_oneway.
Qed.

Lemma AdmissibleDirs_r2_Plus: forall l r,
  AdmissibleDirs (l ++ [Plus; Plus; Minus; Minus] ++ r) -> AdmissibleDirs (l ++ [Plus; Minus] ++ r).
Proof.
	intros l r admds. 
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely_listDir_PPMM _ _ admds) as H.
	destruct H as [ls1 [ls3 [seg1 [seg2 [seg3 [seg4 [Hrightabove [Hslope1 [Hslope2 [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [Hopen Hsparse]]]]]]]]]]]]]];
	try lra; simpl in *.
	assert (Hdir: hd Plus (l ++ Plus :: Minus :: r) = orn (hd_scurve sc)). {
		unfold hd_scurve. unfold scurve_to_direction in Hdir_sc.
		destruct l; simpl in *;
		symmetry; eapply list_map_hd; apply Hdir_sc.
	}
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Plus :: Minus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Plus; Minus; Plus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
	- (* 許容可能であること *)
		pose proof (embedding_PPMM_to_PM_in_rect seg1 seg2 seg3 seg4 Hrightabove Hslope1 Hslope2 Hls2) 
			as [seg1' [seg2' [HPM [Hin_rect [Hinit_term Hslope]]]]].
		(* 欲しかった埋め込み *) 
		exists (ls1 ++ [seg1'; seg2'] ++ ls3). 
		unfold admissible. 
		split.
		+ (* 埋め込みになっていること *) 
			apply (embbeding_inner_change sc sc' l [Plus; Plus; Minus; Minus] [Plus; Minus] r ls1 [seg1; seg2; seg3; seg4] [seg1'; seg2'] ls3); 
				try assumption; try discriminate.
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
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
	intros l r admds.
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely_listDir_MMPP _ _ admds) as H.
	destruct H as [ls1 [ls3 [seg1 [seg2 [seg3 [seg4 [Hrightbelow [Hslope1 [Hslope2 [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [Hopen Hsparse]]]]]]]]]]]]]];
	try lra; simpl in *.
	assert (Hdir: hd Minus (l ++ Minus :: Plus :: r) = orn (hd_scurve sc)). {
		unfold hd_scurve. unfold scurve_to_direction in Hdir_sc.
		destruct l; simpl in *;
		symmetry; eapply list_map_hd; apply Hdir_sc.
	}
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Minus :: Plus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Minus; Plus; Minus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
	- (* 許容可能であること *)
		pose proof (embedding_MMPP_to_MP_in_rect seg1 seg2 seg3 seg4 Hrightbelow Hslope1 Hslope2 Hls2)
			as [seg1' [seg2' [HMP [Hin_rect [Hinit_term Hslope]]]]].
		(* 欲しかった埋め込み *)
		exists (ls1 ++ [seg1'; seg2'] ++ ls3).
		unfold admissible.
		split.
		+ (* 埋め込みになっていること *)
			apply (embbeding_inner_change sc sc' l [Minus; Minus; Plus; Plus] [Minus; Plus] r ls1 [seg1; seg2; seg3; seg4] [seg1'; seg2'] ls3);
				try assumption; try discriminate.
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
			* symmetry. assumption.
		+ (* その埋め込みが開であること *)
			apply (seg_in_rectangle_keep_openness _ _ [seg1; seg2; seg3; seg4] [seg1'; seg2']);
				try assumption; try (symmetry; assumption); try congruence.
			* apply oneway_then_open. apply (embedding_oneway_listDir [Minus; Plus]); try assumption.
			apply MP_is_oneway.
Qed.

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
		symmetry; eapply list_map_hd; apply Hdir_sc.
	}	
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Plus :: Plus :: Minus :: Minus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Plus; Minus; Plus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
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
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
			* symmetry. assumption.
		+ (* その埋め込みが開であること *) 
			apply (seg_in_rectangle_keep_openness _ _ [seg1; seg2] _ ); try assumption; try congruence.
			* apply oneway_then_open. apply (embedding_oneway_listDir [Plus; Plus; Minus; Minus]); try assumption.
				apply PPMM_is_oneway.
Qed.

Lemma AdmissibleDirs_r2_Minus_inv: forall l r,
  AdmissibleDirs (l ++ [Minus; Plus] ++ r) -> AdmissibleDirs (l ++ [Minus; Minus; Plus; Plus] ++ r).
Proof.
	intros l r admds.
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely_listDir _ _ _ admds MP_is_oneway)
		as [ls1 [ls3 [ls2 [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [Hopen Hsparse]]]]]]]];
	simpl in *.
	assert (Hdir: hd Minus (l ++ Minus :: Minus :: Plus :: Plus :: r) = orn (hd_scurve sc)). {
		unfold hd_scurve. unfold scurve_to_direction in Hdir_sc.
		destruct l; simpl in *;
		symmetry; eapply list_map_hd; apply Hdir_sc.
	}
	(* AdmissibleDirs ds の証明では，向きが ds であり許容可能な scurve を1つつくればよい *)
	apply AdmissibleDirs_exist.
	pose proof (direction_scurve_correspondence (tl (l ++ Minus :: Minus :: Plus :: Plus :: r)) (hd_scurve sc))
		as [sc' [Hhead Hdir_sc']].
	exists sc'. split.
	- (* 向きが l ++ [Minus; Plus; Minus] ++ r であること *)
		rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
	- (* 許容可能であること *)
		assert (H: embed_listDir (l ++ [Minus; Plus] ++ r) (ls1 ++ ls2 ++ ls3)). { (* scurve ではなく向き列の方が扱いやすい *)
			unfold embed_listDir. exists sc. split; assumption.
		}
		pose proof (embedding_two_dir Minus Plus ls2 Hls2) as [seg1 [seg2 HMP]]; subst.
		pose proof (embedding_MP_to_MMPP_in_rect _ _ Hls2)
			as [seg1' [seg2' [seg3' [seg4' [HMMPP [Hin_rect [Hinit_term Hslope]]]]]]].
		(* 欲しかった埋め込み *)
		exists (ls1 ++ [seg1'; seg2'; seg3'; seg4'] ++ ls3).
		unfold admissible.
		split.
		+ (* 埋め込みになっていること *)
			apply (embbeding_inner_change sc sc' l [Minus; Plus] [Minus; Minus; Plus; Plus] r ls1 [seg1; seg2] [seg1'; seg2'; seg3'; seg4'] ls3);
				try assumption; try discriminate.
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_hd_tl. destruct l; discriminate.
			* symmetry. assumption.
		+ (* その埋め込みが開であること *)
			apply (seg_in_rectangle_keep_openness _ _ [seg1; seg2] _ ); try assumption; try congruence.
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