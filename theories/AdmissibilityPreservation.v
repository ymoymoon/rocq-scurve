Require Import Admissible.
Require Import Reduction.
Require Import Stdlib.Reals.Reals.
Require Import Embed.
Require Import PrimitiveSegment.
Require Import Segment.
Import ListNotations.


(* 単なるリストに関する補題 *)

Lemma list_head_tail : forall {A} (dummy: A) (l: list A),
	l <> nil -> (hd dummy l) :: (tl l) = l.
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


(* 許容可能性保持の証明に向けた定義と補題群 *)

Parameter slope_init : Segment -> R. (* 傾きを想定しているが，埋め込みの延長線を一意に定義するものであればよい？ *)
Parameter slope_term : Segment -> R.

Definition same_init_and_term (c1 c2 : list Segment) := 
	init (hd default_segment c1) = init (hd default_segment c2) 
	/\ term (last c1 default_segment) = term (last c2 default_segment).

Definition embed_listDir (ds: list Direction) (ls: list Segment) : Prop :=
	exists sc: scurve, scurve_to_direction sc = ds
	/\ embed_scurve sc ls.

(* 単方向 scurve *)
(* TODO: 空リストは含まない．（含めるなら，後の定理の必要な部分に not nil 制約を入れる．） *)
Parameter is_one_way_scurve : scurve -> Prop.

Definition is_one_way_embedding (ls : list Segment) : Prop :=
	exists sc, embed_scurve sc ls /\ is_one_way_scurve sc.
Definition is_one_way_listDir (ds: list Direction) : Prop :=
	exists sc: scurve, scurve_to_direction sc = ds /\ is_one_way_scurve sc.
(* おそらく帰納的に定義することもできる．後者は回転数を使った定義もできる？
		必要があれば証明 *)

(* 曲線の始点と終点を結んだ線分を対角線にもつ矩形．部分曲線を含むとは限らない *)
Parameter rectangular_from_diagonal : R * R -> R * R -> (R * R -> Prop).
Definition in_rect_from_diagonal a b rr := rectangular_from_diagonal a b rr.
Definition in_rect (ls: list Segment) (rr: R * R) := 
	in_rect_from_diagonal (init (hd default_segment ls)) (term (last ls default_segment)) rr.

(* scurve の埋め込みが sub_ls 周りで疎 := sub_ls の始点と終点から作成できる矩形に全然関係ないセグメントが侵入してこない
		sub_ls が開か，全体として開埋め込みかは知らない *)
Definition is_sparse_embedding (sc : scurve) (sub_ls ls : list Segment) : Prop :=
	exists l r, ls = l ++ sub_ls ++ r
	/\ embed_scurve sc ls
	/\ forall rr, 
		(exists seg, onExtendSegment ls seg rr) -> ~ in_rect sub_ls rr.

Definition sparse (sub_ls ls : list Segment) : Prop :=
	exists sc, is_sparse_embedding sc sub_ls ls.

Definition is_sparse_embedding_listDir (ds: list Direction) (sub_ls ls : list Segment) : Prop :=
	exists sc, scurve_to_direction sc = ds
	/\ is_sparse_embedding sc sub_ls ls.


Lemma P_is_oneway : is_one_way_listDir [Plus].
Proof. 
	pose proof (Direction_to_PrimitiveSegment Plus default_primitive_segment) as [p [H _]].
	exists (scurve_from_one p). split.
	- unfold scurve_to_direction. simpl. rewrite H. reflexivity.
	-
Admitted.

Lemma PM_is_oneway : is_one_way_listDir [Plus; Minus].
Proof. 
Admitted.

Lemma PMP_is_oneway : is_one_way_listDir [Plus; Minus; Plus].
Proof.
Admitted.

Lemma PPMM_is_oneway : is_one_way_listDir [Plus; Plus; Minus; Minus].
Proof.
Admitted.

Lemma embedding_oneway_listDir : forall ds ls, 
	embed_listDir ds ls -> is_one_way_listDir ds -> is_one_way_embedding ls.
Proof.
Admitted.

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

Lemma oneway_then_open : forall ls, 
	is_one_way_embedding ls -> ~ close ls.
Proof.
Admitted.


(*【証明の本質としている補題】 許容可能ならば，その中の単方向な sub_ds の埋め込み sub_ls 周りで疎な開埋め込みが存在する *)
Lemma embed_sparsely_listDir (ds1 sub_ds ds2 : list Direction) :
	AdmissibleDirs (ds1 ++ sub_ds ++ ds2)
	-> is_one_way_listDir sub_ds
	-> exists l r sub_ls, 
		embed_listDir ds1 l
		/\ embed_listDir sub_ds sub_ls
		/\ embed_listDir ds2 r
		/\ embed_listDir (ds1 ++ sub_ds ++ ds2) (l ++ sub_ls ++ r)
		/\ ~ close (l ++ sub_ls ++ r)
		/\ sparse sub_ls (l ++ sub_ls ++ r).
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
		/\ sparse sub_ls (l ++ sub_ls ++ r)
		/\ some_good_features.
Proof. Admitted.

(* Plus (の向きを持つ Primitive Segment) の埋め込みを，端点とそこでの傾きを保存したまま
		[Plus; Minus; Plus] の埋め込みとなる３つに矩形内で分割できる *)
Lemma embedding_P_to_PMP_in_rect : forall (seg : Segment),
	embed_listDir [Plus] [seg]
	-> exists seg1 seg2 seg3,
		embed_listDir [Plus; Minus; Plus] [seg1; seg2; seg3] (* この内部で seg1-3 が連結していることは示されてほしい *)
		/\ (forall rr, (exists seg, In seg [seg1; seg2; seg3] /\ onSegment seg rr)
				-> in_rect [seg] rr) (* seg が張る矩形の内部で分割できている *)
		/\ same_init_and_term [seg] [seg1; seg2; seg3]
		/\ slope_init seg = slope_init seg1
		/\ slope_term seg = slope_term seg3.
Proof. Admitted.

(* [Plus; Minus] の埋め込みを，端点とそこでの傾きを保存したまま
		[Plus; Plus; Minus; Minus] の埋め込みとなる4つに矩形内で分割できる *)
Lemma embedding_PM_to_PPMM_in_rect : forall (seg1 seg2 : Segment),
	embed_listDir [Plus; Minus] [seg1; seg2]
	-> exists seg1' seg2' seg3' seg4',
		embed_listDir [Plus; Plus; Minus; Minus] [seg1'; seg2'; seg3'; seg4'] (* この内部で seg1-3 が連結していることは示されてほしい *)
		/\ (forall rr, (exists seg, In seg [seg1'; seg2'; seg3'; seg4'] /\ onSegment seg rr)
				-> in_rect [seg1; seg2] rr) (* seg が張る矩形の内部で分割できている *)
		/\ same_init_and_term [seg1; seg2] [seg1'; seg2'; seg3'; seg4']
		/\ slope_init seg1 = slope_init seg1'
		/\ slope_term seg2 = slope_term seg4'.
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
		/\ slope_init seg1 = slope_init seg
		/\ slope_term seg3 = slope_term seg.
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
		/\ (forall rr, (exists seg, In seg [seg1'; seg2'] /\ onSegment seg rr)
				-> in_rect [seg1; seg2; seg3; seg4] rr) (* seg が張る矩形の内部で分割できている *)
		/\ same_init_and_term [seg1; seg2; seg3; seg4] [seg1'; seg2']
		/\ slope_init seg1 = slope_init seg1'
		/\ slope_term seg4 = slope_term seg2'.
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

(* sub_ls の周りが疎な開埋め込みにおいて，端点で傾きを保ちつつ
		sub_ls をその領域に収まる開な sub_ls' に置き換えても開のまま *)
Lemma seg_in_rectangle_keep_openness : forall (ls rs sub_ls sub_ls' : list Segment), 
	~ close sub_ls'
	-> ~ close (ls ++ sub_ls ++ rs)
	-> sparse sub_ls (ls ++ sub_ls ++ rs)
	-> (forall rr, (exists seg, In seg sub_ls' /\ onSegment seg rr) -> in_rect sub_ls rr) 
	-> same_init_and_term sub_ls sub_ls' 
	-> slope_init (hd default_segment sub_ls) = slope_init (hd default_segment sub_ls')
	-> slope_term (last sub_ls default_segment) = slope_term (last sub_ls' default_segment)
	-> ~ close (ls ++ sub_ls' ++ rs).
Proof. 
	intros ls rs sub_ls sub_ls' Hopen' Hopen Hsparse Hin_rect Hinit_term Hinit_slope Hterm_slope Hclose.
	destruct Hclose as [t1 [t2 [H12 Hsame]]].
	remember (ls ++ sub_ls ++ rs) as pre eqn: E.
	(* 補題：t1, t2 の表す位置は，pre または sub_ls' どちらかの上． *)
	(* t1, t2 の表す位置に関して場合分け *)
	(* 両方が pre 上に存在した場合： pre が開であることに矛盾 *)
	(* 両方が sub_ls' 上に存在した場合： sub_ls' が開であることに矛盾 *)
	(* 一方が pre 上，もう一方が sub_ls' 上に存在した場合： 
		その点は sub_ls から作られる矩形の中にあるので， pre が疎であることから sub_ls, つまり pre 上． 
		pre が開であることに矛盾 *)
Admitted.


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
		pose proof (embedding_PMP_to_P_in_rect seg1 seg2 seg3 Hgood Hls2) as [segP [HP [Hin_rect [Hinit_term [Hinit_slope Hterm_slope]]]]].
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
				try assumption; try (symmetry; assumption).
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
			as [seg1 [seg2 [seg3 [HPMP [Hin_rect [Hinit_term [Hinit_slope Hterm_slope]]]]]]].
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
			apply (seg_in_rectangle_keep_openness _ _ [segP] _ ); try assumption.
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
		pose proof (embedding_PPMM_to_PM_in_rect seg1 seg2 seg3 seg4 Hgood Hls2) as [seg1' [seg2' [HPM [Hin_rect [Hinit_term [Hinit_slope Hterm_slope]]]]]].
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
				try assumption; try (symmetry; assumption).
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
			as [seg1' [seg2' [seg3' [seg4' [HPPMM [Hin_rect [Hinit_term [Hinit_slope Hterm_slope]]]]]]]].
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
			apply (seg_in_rectangle_keep_openness _ _ [seg1; seg2] _ ); try assumption.
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