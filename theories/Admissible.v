From Stdlib Require Export List.
Require Import Reduction.
From Stdlib Require Import ZArith.
Require Import PrimitiveSegment.
Import ListNotations.
Open Scope Z_scope.
Require Import Lia.

Definition all_admissibles :=
[
  (* + *)
  [Plus];
  [Minus];
  (* +- *)
  [Plus; Minus];
  [Minus;Plus];
  (* ++ *)
  [Plus; Plus];
  [Minus; Minus];
  (* +++ *)
  [Plus; Plus; Plus];
  [Minus; Minus; Minus];
  (* ++- *)
  [Plus; Plus; Minus];
  [Minus; Plus; Plus];
  [Minus; Minus; Plus];
  [Plus; Minus; Minus];
  (* +++- *)
  [Plus; Plus; Plus; Minus];
  [Minus; Plus; Plus; Plus];
  [Minus; Minus; Minus; Plus];
  [Plus; Minus; Minus; Minus];
  (* -++- *)
  [Minus; Plus; Plus; Minus];
  [Plus; Minus; Minus; Plus];
  (* ++++- *)
  [Plus; Plus; Plus; Plus; Minus];
  [Minus; Plus; Plus; Plus; Plus];
  [Minus; Minus; Minus; Minus; Plus];
  [Plus; Minus; Minus; Minus; Minus];
  (* -+++- *)
  [Minus; Plus; Plus; Plus; Minus];
  [Plus; Minus; Minus; Minus; Plus];
  (* -++++- *)
  [Minus; Plus; Plus; Plus; Plus; Minus];
  [Plus; Minus; Minus; Minus; Minus; Plus];
  (* -+++++- *)
  [Minus; Plus; Plus; Plus; Plus; Plus; Minus];
  [Plus; Minus; Minus; Minus; Minus; Minus; Plus]
  ].

Parameter AdmissibleDirs : list Direction -> Prop.

Axiom notAdmissibleNil : ~ AdmissibleDirs [].

Lemma nil_reduce ds: ReduceDir ds [] -> ds = [].
Admitted.

Definition reduced ds dsr:= ReduceDir ds dsr /\ ~ CanReduceDirStep dsr. 

Lemma AdmissibleDirs_preserve ds ds': AdmissibleDirs ds -> ReduceDir ds ds' -> AdmissibleDirs ds'.
Admitted.

Axiom inadmissible_rotation_dif_four: forall ds, Z.abs(rotation_difference ds) >= 4 -> ~ AdmissibleDirs ds.

Lemma repeat_dif_P n: rotation_difference (repeat Plus n) = Z.of_nat n.
Admitted. 
Lemma repeat_dif_M n: rotation_difference (repeat Minus n) = - (Z.of_nat n).
Admitted. 

Lemma rotate_dif_four_len_eight ds dsr: reduced ds dsr -> (length dsr >= 8)%nat -> Z.abs(rotation_difference ds) >= 4.
Proof.
  intros [rdc cannotStep] len_eight.
  rewrite (rotation_difference_preservation ds dsr rdc).
  eapply reduced_form in cannotStep as form.
  destruct form as [l [m [n [Hl [Hn [PMP | MPM]]]]]].
  - rewrite PMP in len_eight. repeat rewrite length_app in len_eight. repeat rewrite repeat_length in len_eight. rewrite <- Nat.add_shuffle3 in len_eight. rewrite Nat.add_comm in len_eight.
    destruct l as [| [|l]], n as [| [|n]]; try lia; simpl in len_eight.
    + subst. repeat rewrite rotation_difference_distribution. rewrite repeat_dif_M. repeat rewrite repeat_dif_P. lia.
    + subst. repeat rewrite rotation_difference_distribution. rewrite repeat_dif_M. repeat rewrite repeat_dif_P. lia.
    + subst. repeat rewrite rotation_difference_distribution. rewrite repeat_dif_M. repeat rewrite repeat_dif_P. lia.
    + subst. repeat rewrite rotation_difference_distribution. rewrite repeat_dif_M. repeat rewrite repeat_dif_P. lia.
  - rewrite MPM in len_eight. repeat rewrite length_app in len_eight. repeat rewrite repeat_length in len_eight. rewrite <- Nat.add_shuffle3 in len_eight. rewrite Nat.add_comm in len_eight.
    destruct l as [| [|l]], n as [| [|n]]; try lia; simpl in len_eight;
    subst; repeat rewrite rotation_difference_distribution; rewrite repeat_dif_P; repeat rewrite repeat_dif_M; lia.
Qed.

Ltac listin := repeat (try (now left);right).

Theorem reduced_admissible_form : forall ds dsr, AdmissibleDirs ds -> reduced ds dsr -> In dsr all_admissibles.
Proof.
  intros ds dsr admds [rdc cannotStep].
  eapply reduced_form in cannotStep as form.
  destruct (Nat.le_gt_cases 8 (length dsr)) as [ge8 | lt8];
  [contradict admds; apply inadmissible_rotation_dif_four; eapply rotate_dif_four_len_eight; [split;[exact rdc | exact cannotStep] | exact ge8] |]. 
  destruct form as [l [m [n [lcond [ncond [PMP | MPM]]]]]].
  - destruct l as [|[|l]], n as [|[|n]];simpl in PMP; subst.
    + destruct m as [|[|[|[|m]]]]; try now listin.
      * contradict admds. simpl in rdc. apply nil_reduce in rdc. subst. exact notAdmissibleNil.
      * contradict admds. apply inadmissible_rotation_dif_four. rewrite (rotation_difference_preservation _ _ rdc). rewrite rotation_difference_distribution. rewrite repeat_dif_M. simpl. lia.
    + destruct m as [|[|[|[|[|m]]]]]; try now listin.
      contradict admds. apply inadmissible_rotation_dif_four. rewrite (rotation_difference_preservation _ _ rdc). change (repeat Minus (S (S (S (S (S m)))))) with ([Minus; Minus; Minus; Minus; Minus] ++ repeat Minus m). repeat rewrite rotation_difference_distribution. rewrite repeat_dif_M. rewrite Z.add_comm. rewrite Z.add_assoc. change (rotation_difference [Plus] + rotation_difference [Minus; Minus; Minus; Minus; Minus]) with (-4). lia.
    + contradict ncond. lia.
    + destruct m as [|[|[|[|[|m]]]]]; try now listin.
      contradict admds. apply inadmissible_rotation_dif_four. rewrite (rotation_difference_preservation _ _ rdc). simpl. rewrite app_nil_r. change (Plus :: Minus :: Minus :: Minus :: Minus :: Minus :: repeat Minus m) with ([Plus; Minus; Minus; Minus; Minus; Minus] ++ repeat Minus m). rewrite rotation_difference_distribution. rewrite repeat_dif_M. change (rotation_difference [Plus;Minus; Minus; Minus; Minus; Minus]) with (-4). lia.
    + destruct m as [|[|[|[|[|[|m]]]]]]; try now listin.
      * contradict cannotStep. simpl. exists [Plus]. change ([Plus; Minus; Plus]) with ([] ++ [Plus; Minus; Plus] ++ []). change [Plus] with ([] ++ [Plus] ++ []). now apply RDS.
      * contradict admds. apply inadmissible_rotation_dif_four. rewrite (rotation_difference_preservation _ _ rdc). simpl. repeat rewrite app_comm_cons. change (Plus :: Minus :: Minus :: Minus :: Minus :: Minus :: Minus :: repeat Minus m) with ([Plus; Minus; Minus; Minus; Minus; Minus; Minus] ++ repeat Minus m). repeat rewrite rotation_difference_distribution. rewrite repeat_dif_M. rewrite Z.add_shuffle0. change (rotation_difference [Plus; Minus; Minus; Minus; Minus; Minus; Minus] + rotation_difference [Plus]) with (-4). lia.
    + contradict lcond. lia.
    + contradict lcond. lia.
    + contradict lcond. lia.
    + contradict lcond. lia.
  - destruct l as [|[|l]], n as [|[|n]];simpl in MPM; subst.
    + destruct m as [|[|[|[|m]]]]; try now listin.
      * contradict admds. simpl in rdc. apply nil_reduce in rdc. subst. exact notAdmissibleNil.
      * contradict admds. apply inadmissible_rotation_dif_four. rewrite (rotation_difference_preservation _ _ rdc). rewrite rotation_difference_distribution. rewrite repeat_dif_P. simpl. lia.
    + destruct m as [|[|[|[|[|m]]]]]; try now listin.
      contradict admds. apply inadmissible_rotation_dif_four. rewrite (rotation_difference_preservation _ _ rdc). change (repeat Plus (S (S (S (S (S m)))))) with ([Plus; Plus; Plus; Plus; Plus] ++ repeat Plus m). repeat rewrite rotation_difference_distribution. rewrite repeat_dif_P. rewrite Z.add_comm. rewrite Z.add_assoc. change (rotation_difference [Minus] + rotation_difference [Plus; Plus; Plus; Plus; Plus]) with 4. lia.
    + contradict ncond. lia.
    + destruct m as [|[|[|[|[|m]]]]]; try now listin.
      contradict admds. apply inadmissible_rotation_dif_four. rewrite (rotation_difference_preservation _ _ rdc). simpl. rewrite app_nil_r. change (Minus :: Plus :: Plus :: Plus :: Plus :: Plus :: repeat Plus m) with ([Minus; Plus; Plus; Plus; Plus; Plus] ++ repeat Plus m). rewrite rotation_difference_distribution. rewrite repeat_dif_P. change (rotation_difference [Minus; Plus; Plus; Plus; Plus; Plus]) with 4. lia.
    + destruct m as [|[|[|[|[|[|m]]]]]]; try now listin.
      * contradict cannotStep. simpl. exists [Minus]. change ([Minus; Plus; Minus]) with ([] ++ [Minus; Plus; Minus] ++ []). change [Minus] with ([] ++ [Minus] ++ []). now apply RDS.
      * contradict admds. apply inadmissible_rotation_dif_four. rewrite (rotation_difference_preservation _ _ rdc). simpl. repeat rewrite app_comm_cons. change (Minus :: Plus :: Plus :: Plus :: Plus :: Plus :: Plus :: repeat Plus m) with ([Minus; Plus; Plus; Plus; Plus; Plus; Plus] ++ repeat Plus m). repeat rewrite rotation_difference_distribution. rewrite repeat_dif_P. rewrite Z.add_shuffle0. change (rotation_difference [Minus; Plus; Plus; Plus; Plus; Plus; Plus] + rotation_difference [Minus]) with 4. lia.
    + contradict lcond. lia.
    + contradict lcond. lia.
    + contradict lcond. lia.
    + contradict lcond. lia.
Qed.