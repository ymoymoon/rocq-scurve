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

(* 許容可能性を考えるうえで X1 は適当に固定していい *)
Lemma AdmissibleDirs_head_fix : forall (ds: list Direction) (p: PrimitiveSegment),
	AdmissibleDirs ((orn p) :: ds) <-> 
		(forall sc, 
		hd_scurve sc = p 
		-> scurve_to_direction sc = (orn p) :: ds
		-> admissible sc).
Proof.
	intros ds p. split.
	- auto.
	- intros H.
		(* 1つでも許容可能な scurve を作ればいい *)
		apply AdmissibleDirs_exist.
		pose proof (direction_scurve_correspondence ds p) as [sc [H1 Hsc]].
		exists sc. split.
		+ (* 向き *) rewrite Hsc. reflexivity.
		+ (* 許容可能 *) apply H; try assumption.
Qed.


(* 許容可能性保持の証明に向けた定義と補題群 *)

Parameter slope_init : Segment -> R. (* 傾きを想定しているが，埋め込みの延長線を一意に定義するものであればよい？ *)
Parameter slope_term : Segment -> R.

(* 2次元曲線（連結性を保証）．embed_scurve を使う際はその中で連結性の保証がされるので使用しなくて良い *)
Inductive is_curve : list Segment -> Prop := 
| IsCurveNil : is_curve nil
| IsCurveSingle : forall seg, is_curve [seg]
| IsCurveCons : forall seg1 seg2 segs,
		is_curve (seg2 :: segs)
		-> term seg1 = init seg2
		-> is_curve (seg1 :: seg2 :: segs).

(* Definition curve := {ls : list Segment | is_curve ls}.  *)

Definition same_init_and_term (c1 c2 : list Segment) := (* curve にすべきかも．ただこの方が汎用的か *)
	init (hd default_segment c1) = init (hd default_segment c2) 
	/\ term (last c1 default_segment) = term (last c2 default_segment).

Definition embed_listDir (ds: list Direction) (ls: list Segment) : Prop :=
	exists sc: scurve, scurve_to_direction sc = ds
	/\ embed_scurve sc ls.

(* TODO: 空リストは含まない．（含めるなら，後の定理の必要な部分に not nil 制約を入れる．）繋がっていることも保証． *)
Parameter is_one_way_embedding : list Segment -> Prop
(* Embed.all_same_h 使えそう *).
Definition one_way_embedding := {ls : list Segment | is_one_way_embedding ls}.

(* 単方向 scurve *)
Definition is_one_way_scurve (sc : scurve) : Prop :=
	exists ls, embed_scurve sc ls /\ is_one_way_embedding ls.
Definition is_one_way_listDir (ds: list Direction) : Prop :=
	exists sc: scurve, scurve_to_direction sc = ds /\ is_one_way_scurve sc.
(* おそらく帰納的に定義することもできる．後者は回転数を使った定義もできる？
		必要があれば証明 *)

(* 単方向曲線の始点と終点を結んだ線分を対角線にもつ矩形．部分曲線を含むとは限らない *)
Parameter rectangular_from_diagonal : R * R -> R * R -> (R * R -> Prop).
Definition in_rect_from_diagonal a b rr := rectangular_from_diagonal a b rr.
Definition in_rect (ls: one_way_embedding) rr := 
	in_rect_from_diagonal (init (hd default_segment (proj1_sig ls))) (term (last (proj1_sig ls) default_segment)) rr.

(* 疎：単方向曲線 sub_ls の周囲に全然関係ないセグメントが侵入してこない *)
Definition is_sparse_embedding (sc : scurve) (sub_ls : one_way_embedding) (ls : list Segment) : Prop :=
	exists l r, ls = l ++ (proj1_sig sub_ls) ++ r
	/\ embed_scurve sc ls
	/\ forall rr, 
		(exists seg, onExtendSegment ls seg rr) -> ~ in_rect sub_ls rr.
		(* 下のコメントは，その後曲線を移動させて矩形の縦長横長を操る（ことで端点が絡んでも簡約して端の傾きを保存できるようにする）ことが想定されている．
				人工的かつそのあと曲線の移動が挟まるはずなので，ここで定義を複雑にするより，他の Lemma でうまいことしたい． *)
		(* /\ (l = [] -> (* sub_ls が端点を含む場合，延長線上にも関係ないセグメントが近づかないことを要請 *)
				let X1 := head_seg sub_ls default_segment in 
				let width := (term_x X1) - (init_x X1) in (* 矩形の横幅 *)
				let length := (term_y X1) - (init_y X1) in (* 矩形の縦幅 *)
				forall p, onHeadSegment X1 p -> 
					let rect := rectangular_from_diagonal ((fst p)-width, (snd p)-length) p in (* 矩形 *)
					forall q, 
					(exists seg, onExtendSegment ls seg q /\ ~ onHeadSegment X1 q) 
					-> ~ rect q) *)

Definition sparse (sub_ls : one_way_embedding) (ls : list Segment) : Prop :=
	exists sc, is_sparse_embedding sc sub_ls ls.

Definition is_sparse_embedding_listDir (ds: list Direction) (sub_ls : one_way_embedding) (ls : list Segment) : Prop :=
	exists sc, scurve_to_direction sc = ds
	/\ is_sparse_embedding sc sub_ls ls.


Lemma P_is_oneway : is_one_way_listDir [Plus].
Proof. (* ここは one_way_listDir の定義さえできれば示せる？ *)
Admitted.

Lemma embedding_P_is_oneway : forall seg, 
	embed_listDir [Plus] [seg] -> is_one_way_embedding [seg].
Proof.
Admitted.

Lemma PMP_is_oneway : is_one_way_listDir [Plus; Minus; Plus].
Proof.
Admitted.

Lemma embedding_one_dir : forall d ls, 
	embed_listDir [d] ls -> exists seg, ls = [seg].
Proof. 
	intros d ls H. destruct H as [sc [Hd Hmain]].
	inversion Hmain as [ | ps s | ps lp A s1 s2 ls' H0 Hlp H1 ]; subst.
	- (* if ls = [] *) discriminate.
	- (* if ls = [s], correct *) exists s. reflexivity.
	- (* if ls = s1 :: s2 :: ls' *) 
		unfold scurve_to_direction in Hd.
		unfold connect in Hd. simpl in Hd. 
		inversion Hd as [[H2 Hcontra]].
		destruct lp as [lp H3]; destruct lp as [| head tail].
		+ (* if lp = [] *) simpl in Hlp. inversion Hlp.
		+ (* if lp = head :: tail *) simpl in Hcontra. discriminate.
Qed.

Lemma embedding_is_curve_listDir : forall ls, 
	(exists ds, embed_listDir ds ls) -> is_curve ls.
Proof.
	intros ls H. destruct H as [ds [sc [H1 H2]]].
	induction H2 as [ | | ps lp A s1 s2 ls' Hembed Hconnect IH].
	- (* ls =[] *) apply IsCurveNil.
	- (* ls =[s] *) apply IsCurveSingle.
	- (* ls = s1 :: s2 :: ls' *) apply IsCurveCons.
		+ apply IH. admit. (* IH が弱い *)
		+ assumption.
Admitted.


(* 許容可能ならば，その中の単方向な sub_ds 周りで疎な開埋め込みが存在する．
 		さらに sub_ls の始点と終点とそれぞれでの傾きを（sub_ls の向きを考慮した上で）自由に選んでも良い，
		としたらのちに端点での傾きを保存するために役立つ？ *)
Lemma embed_sparsely_listDir (ds1 sub_ds ds2 : list Direction) :
	AdmissibleDirs (ds1 ++ sub_ds ++ ds2)
	-> is_one_way_listDir sub_ds
	-> exists l r sub_ls, 
		let sub_ls' := proj1_sig sub_ls in
		embed_listDir ds1 l
		/\ embed_listDir sub_ds sub_ls'
		/\ embed_listDir ds2 r
		/\ embed_listDir (ds1 ++ sub_ds ++ ds2) (l ++ sub_ls' ++ r)
		/\ ~ close (l ++ sub_ls' ++ r)
		/\ sparse sub_ls (l ++ sub_ls' ++ r).
Proof. Admitted.

(* 矩形の中にピッタリ収まる1つのセグメントが描ける．端点での傾きは保存されない *)
Lemma embed_in_rectangle : forall (ls : one_way_embedding) (d: Direction), 
	exists seg : Segment, 
		(exists p: PrimitiveSegment, embed p seg /\ orn p = d)
		/\ (forall rr, onSegment seg rr -> in_rect ls rr) 
		/\ same_init_and_term [seg] (proj1_sig ls).
Proof. Admitted.

(* sub_ls の周りが疎な開埋め込みにおいて，端点で傾きを保ちつつ sub_ls をその領域に収まるセグメント列に置き換えても開のまま *)
Lemma seg_in_rectangle_keep_openness : forall sub_ls ls rs (segs: list Segment), (* segs: list Segment にすると，segs の連結性証明が必要 *)
	let sub_ls' := proj1_sig sub_ls in
	~ close (ls ++ sub_ls' ++ rs)
	-> sparse sub_ls (ls ++ sub_ls' ++ rs)
	-> segs <> []
	-> is_curve segs (* 必要と思う *)
	-> slope_init (hd default_segment sub_ls') = slope_init (hd default_segment segs)
	-> slope_term (last sub_ls' default_segment) = slope_term (last segs default_segment)
	-> (forall rr, (exists seg, In seg segs /\ onSegment seg rr) -> in_rect sub_ls rr) 
	-> same_init_and_term segs sub_ls' 
	-> ~ close (ls ++ segs ++ rs).
Proof. Admitted.

(* 傾きの条件を無視できる代わりに，端点を含む置き換えには使えない *)
(* Lemma seg_in_rectangle_keep_openness_old : forall sub_ls l ls r rs seg,
	~ close ((l :: ls) ++ (proj1_sig sub_ls) ++ (r :: rs))
	-> sparse sub_ls ((l :: ls) ++ (proj1_sig sub_ls) ++ (r :: rs))
	-> (forall rr, onSegment seg rr -> in_rect sub_ls rr) 
	-> init seg = init (hd default_segment (proj1_sig sub_ls)) 
	-> term seg = term (last (proj1_sig sub_ls) default_segment)
	-> ~ close ((l :: ls) ++ [seg] ++ (r :: rs)).
Proof. Admitted. *)


(* [+-+ => +] での簡約で，簡約元が許容可能なら簡約先も許容可能 *)
Lemma AdmissibleDirs_r1_Plus: forall l r,
  AdmissibleDirs (l ++ [Plus; Minus; Plus] ++ r) -> AdmissibleDirs (l ++ [Plus] ++ r).
Proof.
	intros l r admds. destruct l as [ | l' l].
	- (* 端点を含む簡約 *) admit.
	- destruct r as [ | r' r].
		+ (* 端点を含む簡約 *) admit.
		+ (* 簡約にかかわった部分の両端に別のセグメントが存在する場合 *)
			unfold AdmissibleDirs. intros ps Hps. unfold admissible.
			pose proof PMP_is_oneway as PMP_is_oneway.
			apply (embed_sparsely_listDir _ _ _ admds) in PMP_is_oneway as 
				[lsl [lsr [sub_ls [Hl [Hr [HPMP [Hopen Hsparse]]]]]]].
			destruct (embed_in_rectangle sub_ls Plus) as 
				[seg [[p [embed_p qrn_p]] [Hin_rect [Hinit Hterm]]]].
			exists (lsl ++ [seg] ++ lsr). split.
			* (* 簡約後の向き列の埋め込みになっていること *) admit.
			* (* その埋め込みが開であること *) admit.
			(* apply seg_in_rectangle_keep_openness. *)
Admitted.

(* Plus (の向きを持つ Primitive Segment) の埋め込みを，[Plus; Minus; Plus] の埋め込みとなる３つに矩形内で分割できる
	TODO：もっと一般的に *)
Lemma P_to_PMP : forall (seg : Segment) (H: embed_listDir [Plus] [seg]),
	exists seg1 seg2 seg3,
		embed_listDir [Plus; Minus; Plus] [seg1; seg2; seg3] (* この内部で seg1-3 が連結していることは示されてほしい *)
		/\ (forall rr, (exists seg, In seg [seg1; seg2; seg3] /\ onSegment seg rr)
				-> in_rect (exist _ [seg] (embedding_P_is_oneway seg H)) rr) (* seg が張る矩形の内部で分割できている *)
		/\ same_init_and_term [seg1; seg2; seg3] [seg]
		/\ slope_init seg = slope_init seg1
		/\ slope_term seg = slope_term seg3.
Proof. Admitted.

(* 簡約前の scurve 内の Plus (の向きを持つ Primitive Segment) の埋め込みを，[Plus; Minus; Plus] の埋め込みに変えたら，
		簡約後の scurve の埋め込みである *)
(* TODO: 向き列を交えずコンパクトにする *)
Lemma P_to_PMP_embbeding : forall sc1 sc2 l r seg seg1 seg2 seg3 ls1 ls2,
	embed_scurve sc1 (ls1 ++ [seg] ++ ls2) (* つまり ls1, seg, ls2 は繋がっている *)
	-> embed_listDir [Plus] [seg]
	-> embed_listDir [Plus; Minus; Plus] [seg1; seg2; seg3]
	-> same_init_and_term [seg1; seg2; seg3] [seg]
	-> scurve_to_direction sc1 = l ++ [Plus] ++ r
	-> scurve_to_direction sc2 = l ++ [Plus; Minus; Plus] ++ r
	-> hd_scurve sc1 = hd_scurve sc2
	-> embed_scurve sc2 (ls1 ++ [seg1; seg2; seg3] ++ ls2).
Proof. Admitted.

(* [+-+ => +] での簡約で，簡約先が許容可能ならもともと許容可能 *)
Lemma AdmissibleDirs_r1_Plus_inv: forall l r,
  AdmissibleDirs (l ++ [Plus] ++ r) -> AdmissibleDirs (l ++ [Plus; Minus; Plus] ++ r).
Proof.
	intros l r admds. 
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely_listDir _ _ _ admds P_is_oneway) as [ls1 [ls3 [[ls2 Honeway] [Hls1 [Hls2 [Hls3 [[sc [Hdir_sc Hembed]] [Hopen Hsparse]]]]]]]];
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
		pose proof (P_to_PMP segP Hls2) as [seg1 [seg2 [seg3 [HPMP [Hin_rect [Hinit_term [Hinit_slope Hterm_slope]]]]]]].
		(* 欲しかった埋め込み *) 
		exists (ls1 ++ [seg1; seg2; seg3] ++ ls3). 
		unfold admissible. 
		split.
		+ (* 埋め込みになっていること *) 
			apply (P_to_PMP_embbeding sc sc' l r segP); try assumption.
			* rewrite Hdir_sc'. rewrite <- Hdir. apply list_head_tail. destruct l; discriminate.
			* symmetry. assumption.
		+ (* その埋め込みが開であること *) 
			apply (seg_in_rectangle_keep_openness (exist _ [segP] (embedding_P_is_oneway segP Hls2))); try assumption.
			(* 仮定を満たすことはほぼ作業的に示せる *)
			* unfold not. intros. discriminate.
			* apply embedding_is_curve_listDir. exists [Plus; Minus; Plus]. assumption.
Qed.

Lemma AdmissibleDirs_r1_Minus_inv: forall l r,
  AdmissibleDirs (l ++ [Minus] ++ r) -> AdmissibleDirs (l ++ [Minus; Plus; Minus] ++ r).
Proof.
Admitted.

Lemma AdmissibleDirs_r2_Plus_inv: forall l r,
  AdmissibleDirs (l ++ [Plus; Minus] ++ r) -> AdmissibleDirs (l ++ [Plus; Plus; Minus; Minus] ++ r).
Proof.
Admitted.

Lemma AdmissibleDirs_r2_Minus_inv: forall l r,
  AdmissibleDirs (l ++ [Minus; Plus] ++ r) -> AdmissibleDirs (l ++ [Minus; Minus; Plus; Plus] ++ r).
Proof.
Admitted.

Lemma AdmissibleDirs_r1_Minus: forall l r,
  AdmissibleDirs (l ++ [Minus; Plus; Minus] ++ r) -> AdmissibleDirs (l ++ [Minus] ++ r).
Proof.
Admitted.

Lemma AdmissibleDirs_r2_Plus: forall l r,
  AdmissibleDirs (l ++ [Plus; Plus; Minus; Minus] ++ r) -> AdmissibleDirs (l ++ [Plus; Minus] ++ r).
Proof.
Admitted.

Lemma AdmissibleDirs_r2_Minus: forall l r,
  AdmissibleDirs (l ++ [Minus; Minus; Plus; Plus] ++ r) -> AdmissibleDirs (l ++ [Minus; Plus] ++ r).
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

