Require Import Stdlib.Lists.List.
Require Import Reduction.
Require Import Stdlib.Reals.Reals.
Require Import Embed.
Require Import PrimitiveSegment.
Require Import Segment.
Import ListNotations.

Parameter default_primitive_segment : PrimitiveSegment.
Parameter slope_init : Segment -> R. (* 傾きを想定しているが，埋め込みの延長線を一意に定義するものであればよい？ *)
Parameter slope_term : Segment -> R.

(* 2次元曲線（連結性を保証）．embed_scurve を使う際はその中で連結性の保証がされるので使用しなくて良い *)
(* Inductive is_curve : list Segment -> Prop := 
| IsCurveNil : is_curve nil
| IsCurveSingle : forall seg, is_curve [seg]
| IsCurveCons : forall seg1 seg2 segs,
		is_curve (seg2 :: segs)
		-> term seg1 = init seg2
		-> is_curve (seg1 :: seg2 :: segs). *)

(* Definition curve := {ls : list Segment | is_curve ls}.  *)

Definition same_init_and_term (c1 c2 : list Segment) := (* curve にすべきかも．ただこの方が汎用的か *)
	init (hd default_segment c1) = init (hd default_segment c2) 
	/\ term (last c1 default_segment) = term (last c2 default_segment).

(* TODO: 空リストは含まない．（含めるなら，後の定理の必要な部分に not nil 制約を入れる．）繋がっていることも保証． *)
Parameter is_one_way_embedding : list Segment -> Prop
(* Embed.all_same_h 使えそう *).
Definition one_way_embedding := {ls : list Segment | is_one_way_embedding ls}.

(* 単方向 scurve *)
Definition is_one_way_scurve (sc : scurve) : Prop :=
	exists ls, embed_scurve sc ls /\ is_one_way_embedding ls.
(* おそらく帰納的に定義することもできる．必要があれば証明 *)

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


Lemma one_pseg_is_scurve : forall (p: PrimitiveSegment), 
	is_scurve [p].
Proof. 
	intros p. apply IsScurveCons.
	- apply IsScurveNil.
	- apply DcNil.
Qed.
	
Definition scurve_from_one p := exist _ _ (one_pseg_is_scurve p).

Lemma dc_pseg_hd_cons : forall x y l,
	dc_pseg_hd x (y ++ l) -> dc_pseg_hd x y.
Proof. 
	intros x y l H.
	destruct y as [| head tail].
	- apply DcNil.
	- apply DcCons. inversion H. assumption.
Qed.

Lemma divide_scurve : forall (sc1 sc2 : list PrimitiveSegment),
	is_scurve (sc1 ++ sc2)
	-> is_scurve sc1 /\ is_scurve sc2.
Proof. 
	intros sc1 sc2 H.
	induction sc1 as [ | head tail IH].
	- (* sc1 =[] *) split.
		+ apply IsScurveNil.
		+ apply H.
	- (* sc1 = head ::tail *) 
		inversion H as [ | x xs Hscurve Hdc]; subst. 
		apply IH in Hscurve as [Htail Hsc2].
		split.
		+ destruct tail as [| head' tail'].
			* (* tail = [] *) apply one_pseg_is_scurve.
			* (* tail = head' :: tail' *) 
				inversion Hdc as [| x y l Hdc']; subst.
				apply (IsScurveCons _ _ Htail).
				apply (dc_pseg_hd_cons _ _ sc2).
				assumption.
		+ assumption.
Qed.

Lemma one_PSeg_is_oneway : forall p, is_one_way_scurve (scurve_from_one p).
Proof. (* ここは is_one_way_scurve の定義さえできれば示せる？ *)
Admitted.

Lemma PMP_is_oneway : forall p1 p2 p3 (Hscurve: is_scurve [p1; p2; p3]), 
	orn p1 = Plus
	-> orn p2 = Minus
	-> orn p3 = Plus
	-> is_one_way_scurve (exist _ _ Hscurve).
Proof. (* ここは is_one_way_scurve の定義さえできれば示せる？ *)
Admitted.

Lemma embedding_one : forall p ls, 
	embed_scurve (scurve_from_one p) ls -> exists seg, ls = [seg].
Proof. 
	intros p ls H.
	inversion H as [ | ps s | ps [lp H0] A s1 s2 ls' H1 Hlp H2]; subst.
	- (* if ls = [s], correct *) exists s. reflexivity.
	- (* if ls = s1 :: s2 :: ls' *) inversion Hlp.
Qed.

Lemma embedding_one_is_oneway : forall p seg, 
	embed_scurve (scurve_from_one p) [seg] -> is_one_way_embedding [seg].
Proof.
Admitted.

Lemma embedding_PMP_is_oneway : forall seg1 seg2 seg3 p1 p2 p3 (Hscurve: is_scurve [p1; p2; p3]), 
	embed_scurve (exist _ _ Hscurve) [seg1; seg2; seg3] 
	-> orn p1 = Plus
	-> orn p2 = Minus
	-> orn p3 = Plus
	-> is_one_way_embedding [seg1; seg2; seg3].
Proof.
Admitted.

(* [Plus; Plus; Minus; Minus] -> [Plus; Minus] の簡約で，先頭と末尾の PrimitiveSegment は変化しない *)
Lemma r2_same_head_and_term_PPMM : forall p1 p2 p3 p4 p4'
	(Hbefore: is_scurve [p1; p2; p3; p4])
	(Hafter: is_scurve [p1; p4']),
	scurve_to_direction (exist _ _ Hbefore) = [Plus; Plus; Minus; Minus]
	-> scurve_to_direction (exist _ _ Hafter) = [Plus; Minus]
	-> p4 = p4'.
Proof. 
	unfold scurve_to_direction. simpl. 
	intros p1 p2 p3 p4 p4' Hbefore Hafter Hdir1 Hdir2.
	inversion Hdir1 as [[H1 H2 H3 H4]]; clear Hdir1.
	rewrite H1 in H2. rewrite H3 in H4.
	inversion Hdir2 as [[H1' H4']]; clear Hdir2.
	inversion Hbefore as [ | x xs H234 Hdc1]; subst; clear Hbefore.
	inversion H234 as [ | x xs H34 Hdc2]; subst; clear H234.
	inversion H34 as [ | x xs _ Hdc3]; subst; clear H34.
	inversion Hdc1 as [ | x y l Hdc12]; subst; clear Hdc1.
	inversion Hdc2 as [ | x y l Hdc23]; subst; clear Hdc2.
	inversion Hdc3 as [ | x y l Hdc34]; subst; clear Hdc3.
	inversion Hafter as [ | x xs _ Hdc14']; subst; clear Hafter.
	inversion Hdc14' as [ | x y l Hdc14]; subst; clear Hdc14'. 
	(* 直接連結の定義で場合わけあるのみ．所々で場合を潰さないと重くなる *)
	inversion Hdc12 as [v1 h c1 | h | h | h | h]; subst; destruct h; try discriminate;
	inversion Hdc23; subst; try discriminate;
	inversion Hdc34; subst; try discriminate;
	inversion Hdc14; subst; try discriminate; try reflexivity;
	destruct c1; try discriminate; try reflexivity.
Qed.

(* [Minus; Minus; Plus; Plus] -> [Minus; Plus] の簡約で，先頭と末尾の PrimitiveSegment は変化しない *)
Lemma r2_same_head_and_term_MMPP : forall p1 p2 p3 p4 p4'
	(Hbefore: is_scurve [p1; p2; p3; p4])
	(Hafter: is_scurve [p1; p4']),
	scurve_to_direction (exist _ _ Hbefore) = [ Minus; Minus; Plus; Plus]
	-> scurve_to_direction (exist _ _ Hafter) = [Minus; Plus]
	-> p4 = p4'.
Proof. unfold scurve_to_direction. simpl. 
	intros p1 p2 p3 p4 p4' Hbefore Hafter Hdir1 Hdir2.
	inversion Hdir1 as [[H1 H2 H3 H4]]; clear Hdir1.
	rewrite H1 in H2. rewrite H3 in H4.
	inversion Hdir2 as [[H1' H4']]; clear Hdir2.
	inversion Hbefore as [ | x xs H234 Hdc1]; subst; clear Hbefore.
	inversion H234 as [ | x xs H34 Hdc2]; subst; clear H234.
	inversion H34 as [ | x xs _ Hdc3]; subst; clear H34.
	inversion Hdc1 as [ | x y l Hdc12]; subst; clear Hdc1.
	inversion Hdc2 as [ | x y l Hdc23]; subst; clear Hdc2.
	inversion Hdc3 as [ | x y l Hdc34]; subst; clear Hdc3.
	inversion Hafter as [ | x xs _ Hdc14']; subst; clear Hafter.
	inversion Hdc14' as [ | x y l Hdc14]; subst; clear Hdc14'. 
	(* 直接連結の定義で場合わけあるのみ．所々で場合を潰さないと重くなる *)
	inversion Hdc12 as [v1 h c1 | h | h | h | h]; subst; destruct h; try discriminate;
	inversion Hdc23; subst; try discriminate;
	inversion Hdc34; subst; try discriminate;
	inversion Hdc14; subst; try discriminate; try reflexivity;
	destruct c1; try discriminate; try reflexivity.
Qed.

(* sub_ls の周りが疎な開埋め込みにおいて，端点で傾きを保ちつつ sub_ls をその領域に収まる単方向な埋め込みに置き換えても開のまま *)
(* 単方向でない埋め込みに変えるならそこで自己交差しないことの，またsegs: list Segment にすると segs の連結性証明がそれぞれ必要 *)
Lemma seg_in_rectangle_keep_openness : forall ls rs (sub_ls segs: one_way_embedding), 
	let sub_ls' := proj1_sig sub_ls in
	let segs' := proj1_sig segs in
	~ close (ls ++ sub_ls' ++ rs)
	-> sparse sub_ls (ls ++ sub_ls' ++ rs)
	-> segs' <> []
	-> slope_init (hd default_segment sub_ls') = slope_init (hd default_segment segs')
	-> slope_term (last sub_ls' default_segment) = slope_term (last segs' default_segment)
	-> (forall rr, (exists seg, In seg segs' /\ onSegment seg rr) -> in_rect sub_ls rr) 
	-> same_init_and_term segs' sub_ls' 
	-> ~ close (ls ++ segs' ++ rs).
Proof. Admitted.

(* 許容可能ならば，その中の単方向な sub_sc 周りで疎な開埋め込みが存在する．
 		さらに sub_ls の始点と終点とそれぞれでの傾きを（sub_ls の向きを考慮した上で）自由に選んでも良い，
		としたらのちに端点での傾きを保存するために役立つ？ *)
(* TODO： sub_sc も scurve か one_way_scurve のほうが統一的 *)
Lemma embed_sparsely sc1 sub_sc sc2
	(Hall: is_scurve ((proj1_sig sc1) ++ sub_sc ++ (proj1_sig sc2)))
	(Hsub: is_scurve sub_sc) :
	admissible (exist _ _ Hall)
	-> is_one_way_scurve (exist _ _ Hsub)
	-> exists ls1 ls2 (sub_ls: one_way_embedding), 
	let sub_ls' := proj1_sig sub_ls in
		embed_scurve sc1 ls1
		/\ embed_scurve (exist _ _ Hsub) sub_ls'
		/\ embed_scurve sc2 ls2
		/\ embed_scurve (exist _ _ Hall) (ls1 ++ sub_ls' ++ ls2)
		/\ ~ close (ls1 ++ sub_ls' ++ ls2)
		/\ sparse sub_ls (ls1 ++ sub_ls' ++ ls2).
Proof. Admitted.

(* TODO：some good features を具体化（引数要るだろう）して上の補題に統合する
		embed_sparsely 上のコメントが有望か *)
Parameter some_good_features : Prop.

Lemma embed_sparsely_with_good_features sc1 sub_sc sc2
	(Hall: is_scurve ((proj1_sig sc1) ++ sub_sc ++ (proj1_sig sc2)))
	(Hsub: is_scurve sub_sc) :
	admissible (exist _ _ Hall)
	-> is_one_way_scurve (exist _ _ Hsub)
	-> exists ls1 ls2 (sub_ls: one_way_embedding), 
	let sub_ls' := proj1_sig sub_ls in
		embed_scurve sc1 ls1
		/\ embed_scurve (exist _ _ Hsub) sub_ls'
		/\ embed_scurve sc2 ls2
		/\ embed_scurve (exist _ _ Hall) (ls1 ++ sub_ls' ++ ls2)
		/\ ~ close (ls1 ++ sub_ls' ++ ls2)
		/\ sparse sub_ls (ls1 ++ sub_ls' ++ ls2)
		/\ some_good_features.
Proof. Admitted.

(* p1 の埋め込みを，[p1; p2; p3] (ただし向きは [Plus; Minus; Plus] ) の埋め込みとなる３つに矩形内で分割できる *)
Lemma embedding_P_to_PMP_in_rect : forall p1 p2 p3 (seg : Segment) 
	(Hembed: embed_scurve (scurve_from_one p1) [seg])
	(Hscurve: is_scurve [p1; p2; p3]),
	scurve_to_direction (exist _ _ Hscurve) = [Plus; Minus; Plus]
	-> exists seg1 seg2 seg3,
			embed_scurve (exist _ _ Hscurve) [seg1; seg2; seg3] (* この内部で seg1-3 が連結していることは示されてほしい *)
			/\ (forall rr, (exists seg, In seg [seg1; seg2; seg3] /\ onSegment seg rr)
					-> in_rect (exist _ [seg] (embedding_one_is_oneway p1 seg Hembed)) rr) (* seg が張る矩形の内部で分割できている *)
			/\ same_init_and_term [seg1; seg2; seg3] [seg]
			/\ slope_init seg = slope_init seg1
			/\ slope_term seg = slope_term seg3.
Proof. Admitted.

(* good features があれば，[p1; p2; p3] (ただし向きは [Plus; Minus; Plus] ) の埋め込みを，p1 の埋め込みに矩形内で変更できる *)
(* TODO：傾きも保存できるような good features を見つけて具体化 *)
Lemma embedding_PMP_to_P_in_rect : forall p1 p2 p3 (seg1 seg2 seg3 : Segment) 
	(Hscurve: is_scurve [p1; p2; p3])
	(Hembed: embed_scurve (exist _ _ Hscurve) [seg1; seg2; seg3])
	(Hp1: orn p1 = Plus) (Hp2: orn p2 = Minus) (Hp3: orn p3 = Plus),
	some_good_features
	-> scurve_to_direction (exist _ _ Hscurve) = [Plus; Minus; Plus]
	-> exists seg,
			embed_scurve (scurve_from_one p1) [seg]
			/\ (forall rr, onSegment seg rr
					-> in_rect (exist _ [seg1; seg2; seg3] (embedding_PMP_is_oneway _ _ _ _ _ _ _ Hembed Hp1 Hp2 Hp3)) rr)
			/\ same_init_and_term [seg1; seg2; seg3] [seg]
			/\ slope_init seg = slope_init seg1
			/\ slope_term seg = slope_term seg3.
Proof. Admitted.

(* 簡約前の scurve 内の p1 の埋め込みを，[p1; p2; p3] (ただし向きは [Plus; Minus; Plus] ) の埋め込みに変えたら，
		簡約後の scurve の埋め込みである *)
Lemma embedding_inner_P_to_PMP : forall (p1 p2 p3: PrimitiveSegment) (pre post: scurve) (seg seg1 seg2 seg3: Segment) ls1 ls2
	(Hbefore: is_scurve ((proj1_sig pre) ++ [p1] ++ (proj1_sig post)))
	(Hafter: is_scurve ((proj1_sig pre) ++ [p1; p2; p3] ++ (proj1_sig post))) (* 本当は Hafter だけで内部が scurve だとわかるが *)
	(Hmid: is_scurve [p1; p2; p3]),
	scurve_to_direction (exist _ _ Hmid) = [Plus; Minus; Plus]
	-> embed_scurve (exist _ _ Hbefore) (ls1 ++ [seg] ++ ls2) (* つまり ls1, seg, ls2 は繋がっている *)
	-> embed_scurve (scurve_from_one p1) [seg]
	-> embed_scurve (exist _ _ Hmid) [seg1; seg2; seg3]
	-> same_init_and_term [seg1; seg2; seg3] [seg]
	-> embed_scurve (exist _ _ Hafter) (ls1 ++ [seg1; seg2; seg3] ++ ls2).
Proof. Admitted.

(* [+-+ => +] での簡約で，簡約先が許容可能ならもともと許容可能．Hbefore から Hafter は導けるが，それは別の補題で *)
Lemma admissible_r1_Plus_inv: forall (p1 p2 p3: PrimitiveSegment) (pre post: scurve)
	(Hbefore: is_scurve ((proj1_sig pre) ++ [p1; p2; p3] ++ (proj1_sig post))) 
	(Hafter: is_scurve ((proj1_sig pre) ++ [p1] ++ (proj1_sig post))),
	orn p1 = Plus 
	-> orn p2 = Minus
	-> orn p3 = Plus
  -> admissible (exist _ _ Hafter) 
	-> admissible (exist _ _ Hbefore).
Proof.
	intros p1 p2 p3 pre post Hbefore Hafter Hp1 Hp2 Hp3 Hadm.
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely _ _ _ Hafter (one_pseg_is_scurve p1) Hadm (one_PSeg_is_oneway p1)) as [ls1 [ls3 [[ls2 Honeway] [Hls1 [Hls2 [Hls3 [Hembed [Hopen Hsparse]]]]]]]];
	simpl in *. 
	(* pre, p1, post に対応する埋め込みを抽出 *)
	pose proof (embedding_one _ ls2 Hls2) as [seg2' H2]; subst.
	(* p1 の埋め込みを，[Plus; Minus; Plus] の埋め込みになるよう３つに分解 *)
	pose proof (divide_scurve _ _ Hbefore) as [_ H].
	apply (divide_scurve [p1; p2; p3] _) in H as [H123 _].
	assert (HPMP: scurve_to_direction (exist _ _ H123) = [Plus; Minus; Plus]). {
		unfold scurve_to_direction. simpl. rewrite Hp1. rewrite Hp2. rewrite Hp3. reflexivity.
	}
	pose proof (embedding_P_to_PMP_in_rect _ _ _ seg2' Hls2 H123 HPMP) as [seg1 [seg2 [seg3 [Hseg123 [Hin_rect [Hinit_term [Hinit_slope Hterm_slope]]]]]]].
	(* 欲しかった埋め込み *)
	exists (ls1 ++ [seg1; seg2; seg3] ++ ls3). 
	unfold admissible. 
	split.
	- (* 埋め込みになっていること *) 
		apply (embedding_inner_P_to_PMP _ _ _ _ _ seg2' seg1 seg2 seg3 ls1 ls3 Hafter Hbefore H123); 
		try assumption.
	- (* その埋め込みが開であること *) 
		apply (seg_in_rectangle_keep_openness _ _ 
			(exist _ [seg2'] (embedding_one_is_oneway _ _ Hls2))
			(exist _ _ (embedding_PMP_is_oneway _ _ _ _ _ _ _ Hseg123 Hp1 Hp2 Hp3))); 
		try assumption.
		(* 仮定を満たすことはほぼ作業的に示せる *)
		+ unfold not. intros. discriminate.
Qed.


Lemma admissible_r1_Minus_inv: forall (p1 p2 p3: PrimitiveSegment) (pre post: scurve)
	(Hbefore: is_scurve ((proj1_sig pre) ++ [p1; p2; p3] ++ (proj1_sig post))) 
	(Hafter: is_scurve ((proj1_sig pre) ++ [p1] ++ (proj1_sig post))),
	orn p1 = Minus 
	-> orn p2 = Plus
	-> orn p3 = Minus
  -> admissible (exist _ _ Hafter) 
	-> admissible (exist _ _ Hbefore).
Proof.
Admitted.

Lemma admissible_r2_Plus_inv: forall (p1 p2 p3 p4: PrimitiveSegment) (pre post: scurve)
	(Hbefore: is_scurve ((proj1_sig pre) ++ [p1; p2; p3; p4] ++ (proj1_sig post))) 
	(Hafter: is_scurve ((proj1_sig pre) ++ [p1; p4] ++ (proj1_sig post))),
	orn p1 = Plus 
	-> orn p2 = Plus
	-> orn p3 = Minus
	-> orn p4 = Minus
  -> admissible (exist _ _ Hafter) 
	-> admissible (exist _ _ Hbefore).
Proof.
Admitted.

Lemma admissible_r2_Minus_inv: forall (p1 p2 p3 p4: PrimitiveSegment) (pre post: scurve)
	(Hbefore: is_scurve ((proj1_sig pre) ++ [p1; p2; p3; p4] ++ (proj1_sig post))) 
	(Hafter: is_scurve ((proj1_sig pre) ++ [p1; p4] ++ (proj1_sig post))),
	orn p1 = Minus 
	-> orn p2 = Minus
	-> orn p3 = Plus
	-> orn p4 = Plus
  -> admissible (exist _ _ Hafter) 
	-> admissible (exist _ _ Hbefore).
Proof.
Admitted.

Lemma admissible_r1_Plus: forall (p1 p2 p3: PrimitiveSegment) (pre post: scurve)
	(Hbefore: is_scurve ((proj1_sig pre) ++ [p1; p2; p3] ++ (proj1_sig post))) 
	(Hafter: is_scurve ((proj1_sig pre) ++ [p1] ++ (proj1_sig post))),
	orn p1 = Plus 
	-> orn p2 = Minus
	-> orn p3 = Plus
  -> admissible (exist _ _ Hbefore) 
	-> admissible (exist _ _ Hafter).
Proof.
	intros p1 p2 p3 pre post Hbefore Hafter Hp1 Hp2 Hp3 Hadm.
	(* [p1; p2; p3] が scurve である証拠を抽出 *)
	pose proof (divide_scurve _ _ Hbefore) as [_ H].
	apply (divide_scurve [p1; p2; p3] _) in H as [H123 _].
	(* 疎な開埋め込みをとる *)
	pose proof (embed_sparsely_with_good_features _ _ _ Hbefore H123 Hadm (PMP_is_oneway _ _ _ H123 Hp1 Hp2 Hp3)) 
		as [ls1 [ls3 [[ls2 Honeway] [Hls1 [Hls2 [Hls3 [Hembed [Hopen [Hsparse Hgood]]]]]]]]];
	simpl in *. 
	(* pose proof (embedding_PMP_to_P_in_rect _ _ _ _ _ _ H123 Hls2 H123 Hgood HPMP) 
		as [seg1 [seg2 [seg3 [Hseg123 [Hin_rect [Hinit_term [Hinit_slope Hterm_slope]]]]]]]. *)
Admitted.

Lemma admissible_r1_Minus: forall (p1 p2 p3: PrimitiveSegment) (pre post: scurve)
	(Hbefore: is_scurve ((proj1_sig pre) ++ [p1; p2; p3] ++ (proj1_sig post))) 
	(Hafter: is_scurve ((proj1_sig pre) ++ [p1] ++ (proj1_sig post))),
	orn p1 = Minus 
	-> orn p2 = Plus
	-> orn p3 = Minus
  -> admissible (exist _ _ Hbefore) 
	-> admissible (exist _ _ Hafter).
Proof.
Admitted.

Lemma admissible_r2_Plus: forall (p1 p2 p3 p4: PrimitiveSegment) (pre post: scurve)
	(Hbefore: is_scurve ((proj1_sig pre) ++ [p1; p2; p3; p4] ++ (proj1_sig post))) 
	(Hafter: is_scurve ((proj1_sig pre) ++ [p1; p4] ++ (proj1_sig post))),
	orn p1 = Plus 
	-> orn p2 = Plus
	-> orn p3 = Minus
	-> orn p4 = Minus
  -> admissible (exist _ _ Hbefore) 
	-> admissible (exist _ _ Hafter).
Proof.
Admitted.

Lemma admissible_r2_Minus: forall (p1 p2 p3 p4: PrimitiveSegment) (pre post: scurve)
	(Hbefore: is_scurve ((proj1_sig pre) ++ [p1; p2; p3; p4] ++ (proj1_sig post))) 
	(Hafter: is_scurve ((proj1_sig pre) ++ [p1; p4] ++ (proj1_sig post))),
	orn p1 = Minus 
	-> orn p2 = Minus
	-> orn p3 = Plus
	-> orn p4 = Plus
  -> admissible (exist _ _ Hbefore) 
	-> admissible (exist _ _ Hafter).
Proof.
Admitted.


(* Reduction.Reduce は下の Reduce_scurve にすべき？ おそらく許容可能性的にはどちらでも問題ない．
	3つの PSeg からなる [(n, e, cx), (n, e, cc), (n, e, cx)] (向きは [Plus; Minus; Plus]) を 
	[((s, e, cx))] (向きは [Plus]) に簡約する，ということを認めるかどうか *)
Definition ReduceRule (sc sc': scurve) := 
	Rule (scurve_to_direction sc) (scurve_to_direction sc') 
	/\ hd default_primitive_segment (proj1_sig sc) = hd default_primitive_segment (proj1_sig sc').

Definition ReduceStep (sc sc': scurve) := 
	ReduceDirStep (scurve_to_direction sc) (scurve_to_direction sc') 
	/\ hd default_primitive_segment (proj1_sig sc) = hd default_primitive_segment (proj1_sig sc').

Definition Reduce_scurve (sc sc': scurve) := 
	ReduceDir (scurve_to_direction sc) (scurve_to_direction sc') 
	/\ hd default_primitive_segment (proj1_sig sc) = hd default_primitive_segment (proj1_sig sc').

Lemma admissiblity_preservation_Rule : forall (pre sub_sc sub_sc' post: scurve)
	(Hbefore: is_scurve ((proj1_sig pre) ++ (proj1_sig sub_sc) ++ (proj1_sig post))) 
	(Hafter: is_scurve ((proj1_sig pre) ++ (proj1_sig sub_sc') ++ (proj1_sig post))),
  ReduceRule sub_sc sub_sc'
	-> (admissible (exist _ _ Hbefore) <-> admissible (exist _ _ Hafter)).
Proof.
	intros pre sub_sc sub_sc' post Hbefore Hafter [Hrule Hhead]. 
	inversion Hrule as [ HPMP HP | HMPM HM | HPPMM HPM | HMMPP HMP ]; subst. 
	- (* +-+ -> + *)
			unfold scurve_to_direction in HPMP. destruct sub_sc as [sc P]; simpl in *. 
			(* sub_sc = [h1; h2; h3], sub_sc' = [h1] を導く *)
			destruct sc as [ | h1 tail ]; try discriminate.
			destruct tail as [ | h2 tail ]; try discriminate.
			destruct tail as [ | h3 tail ]; try discriminate.
			destruct tail as [ | ]; try discriminate.
			unfold scurve_to_direction in HP. destruct sub_sc' as [sc P']; simpl in *. 
			destruct sc as [ | h1' tail ]; try discriminate.
			destruct tail as [ | ]; try discriminate.
			inversion HP. simpl in Hhead; subst.
			split.
			+ apply admissible_r1_Plus; inversion HPMP; reflexivity.
			+ apply admissible_r1_Plus_inv; inversion HPMP; reflexivity.
	- (* -+- -> - *) 
			unfold scurve_to_direction in HMPM. destruct sub_sc as [sc P]; simpl in *. 
			(* sub_sc = [h1; h2; h3], sub_sc' = [h1] を導く *)
			destruct sc as [ | h1 tail ]; try discriminate.
			destruct tail as [ | h2 tail ]; try discriminate.
			destruct tail as [ | h3 tail ]; try discriminate.
			destruct tail as [ | ]; try discriminate.
			unfold scurve_to_direction in HM. destruct sub_sc' as [sc P']; simpl in *. 
			destruct sc as [ | h1' tail ]; try discriminate.
			destruct tail as [ | ]; try discriminate.
			inversion HM. simpl in Hhead; subst.
			split.
			+ apply admissible_r1_Minus; inversion HMPM; reflexivity.
			+ apply admissible_r1_Minus_inv; inversion HMPM; reflexivity.
	- (* ++-- -> +- *) 
			unfold scurve_to_direction in HPPMM. destruct sub_sc as [sc P]; simpl in *. 
			(* sub_sc = [h1; h2; h3; h4], sub_sc' = [h1; h4] を導く *)
			destruct sc as [ | h1 tail ]; try discriminate.
			destruct tail as [ | h2 tail ]; try discriminate.
			destruct tail as [ | h3 tail ]; try discriminate.
			destruct tail as [ | h4 tail ]; try discriminate.
			destruct tail as [ | ]; try discriminate.
			unfold scurve_to_direction in HPM. destruct sub_sc' as [sc P']; simpl in *. 
			destruct sc as [ | h1' tail ]; try discriminate.
			destruct tail as [ | h4' tail ]; try discriminate.
			destruct tail as [ | ]; try discriminate.
			inversion HPM. simpl in Hhead; subst.
			assert (H: h4 = h4'). {
				apply (r2_same_head_and_term_PPMM _ _ _ _ _ P P'); unfold scurve_to_direction; simpl.
				+ rewrite HPPMM. reflexivity.
				+ rewrite HPM. reflexivity.
			} subst.
			split.
			+ apply admissible_r2_Plus; inversion HPPMM; reflexivity.
			+ apply admissible_r2_Plus_inv; inversion HPPMM; reflexivity.
	- (* --++ -> -+ *) 
			unfold scurve_to_direction in HMMPP. destruct sub_sc as [sc P]; simpl in *. 
			(* sub_sc = [h1; h2; h3; h4], sub_sc' = [h1; h4] を導く *)
			destruct sc as [ | h1 tail ]; try discriminate.
			destruct tail as [ | h2 tail ]; try discriminate.
			destruct tail as [ | h3 tail ]; try discriminate.
			destruct tail as [ | h4 tail ]; try discriminate.
			destruct tail as [ | ]; try discriminate.
			unfold scurve_to_direction in HMP. destruct sub_sc' as [sc P']; simpl in *. 
			destruct sc as [ | h1' tail ]; try discriminate.
			destruct tail as [ | h4' tail ]; try discriminate.
			destruct tail as [ | ]; try discriminate.
			inversion HMP. simpl in Hhead; subst.
			assert (H: h4 = h4'). {
				apply (r2_same_head_and_term_MMPP _ _ _ _ _ P P'); unfold scurve_to_direction; simpl.
				+ rewrite HMMPP. reflexivity.
				+ rewrite HMP. reflexivity.
			} subst.
			split.
			+ apply admissible_r2_Minus; inversion HMMPP; reflexivity.
			+ apply admissible_r2_Minus_inv; inversion HMMPP; reflexivity.
Qed.

Lemma admissiblity_preservation_step : forall (sc sc': scurve),
  ReduceStep sc sc'
	-> (admissible sc <-> admissible sc').
Proof.
	intros sc sc' [Hreduce Hhead].
	inversion Hreduce as [l r ds ds' Hrule Hbefore Hafter].
Admitted.

Theorem admissiblity_preservation : forall (sc sc': scurve),
  Reduce_scurve sc sc'
	-> (admissible sc <-> admissible sc').
Proof.
	intros sc sc' [Hreduce Hhead].
Admitted.