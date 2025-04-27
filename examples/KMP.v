Require Import SetsClass.SetsClass.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
From SetMonad Require Import Monad SetMonad SetHoare.
Require Import Examples.ListLib.
Import SetsNotation
       SetMonad
       Monad
       MonadNotation.
Local Open Scope sets.
Local Open Scope nat.
Local Open Scope monad.
Local Open Scope list.

Import SetMonadHoare
       SetMonadTactic
       ListNotations.

(** The formal definition of match procedure and the table-building procedure *)
Section algo_def.
Context {A: Type}
        (default: A)
        (patn text: list A).

Definition inner_body (next: list nat) (ch: A) : nat -> program (CntOrBrk nat nat) :=
  fun j =>
    choice 
     (assume(ch = nth j patn default);; break (j+1))
     (assume(ch <> nth j patn default);;
      choice 
       (assume(j = 0);; break 0) 
       (assume(j <> 0);; continue (nth (j-1) next 0))).

Definition inner_loop (next: list nat) (ch: A) : nat -> program nat :=
  repeat_break (inner_body next ch).

Definition match_body (next: list nat):
  (nat * nat) -> program (CntOrBrk nat nat) :=
  fun '(i, j) =>
      let ch := nth i text default in
      j' <- inner_loop next ch j;;
      choice
        (assume (j' = length patn);;
         break (i + 1 - length patn))
        (assume (j' < length patn);;
         continue (j')).

Definition match_loop (next: list nat): program (CntOrBrk nat nat) :=
  range_iter_break 0 (length text) (match_body next) 0.

(** The table-building procedure *)
Definition constr_body:
  (nat * (list nat * nat)) -> program (list nat * nat) :=
    fun '(i, (next, j)) =>
      let ch := nth i patn default in
      j' <- inner_loop next ch j;;
      ret (next ++ [j'], j').

Definition contsr_loop: program (list nat) :=
  '(next, _) <- range_iter 1 (length patn) constr_body ([0], 0);;
  ret next.

End algo_def.

Section match_proof.
Context {A: Type}
        (default: A)
        (patn text: list A)
        (next: list nat).

Definition prefix_func (next: list nat): Prop :=
  forall i0: nat,
    0 <= i0 < length next ->
    max_proper_presuffix
      (sublist 0 (nth i0 next 0) patn)
      (sublist 0 (i0 + 1) patn).

Definition no_occur (i: nat) :=
  forall j, 0 <= j < i + 1 - length patn -> 
    sublist j (j + length patn) text <> patn.

Definition first_occur (i: nat) :=
  sublist i (i + length patn) text = patn /\
  no_occur (i + length patn - 1).

(** The goal of match_proof *) 
Definition match_pre :=
  patn <> nil /\
  length next = length patn /\
  prefix_func next.

Definition match_post (r: CntOrBrk nat nat) :=
  match r with
  | by_break i => first_occur i
  | by_continue i => no_occur (length text)
  end.

(** Stage 1: Essential Proof *)
(** Group 1: range *)
Definition jrange (j: nat) :=
  0 <= j < length next.
        
Lemma jrange_init:
  patn <> nil -> length next = length patn ->
  jrange 0.
Proof.
  intros.
  apply length_nonnil in H.
  unfold jrange; lia.
Qed.


Lemma inner_pre_prefix_imply:
  prefix_func next ->
  (forall k, jrange k ->
    0 <= nth k next 0 <= k).
Proof.
  intros.
  unfold jrange in H.
  unfold prefix_func in H.
  specialize (H _ H0).
  destruct H as [[_ H] _].
  rewrite (length_sublist' _ _ (k+1)) in H.
  rewrite length_sublist' in H.
  lia.
Qed.

Lemma inner_range_cnt (i j: nat):
  (forall k, jrange k ->
    0 <= nth k next 0 <= k) ->
  jrange j ->
  Hoare (x <- inner_body default patn next (nth i text default) j;; continue_case x)
        (fun j' => jrange j').
Proof.
  intros; unfold jrange in *.
  unfold inner_body.
  hoare_auto.
  specialize (H (j-1) ltac:(lia)).
  lia.
Qed.

Lemma inner_range_brk (i j: nat):
  jrange j ->
  Hoare (x <- inner_body default patn next (nth i text default) j;; break_case x)
        (fun j' => 0 <= j' <= length next).
Proof.
  intros; unfold jrange in *.
  unfold inner_body; hoare_auto; lia.
Qed.

Lemma match_range_cnt (j: nat):
  length next = length patn ->
  0 <= j <= length next ->
  Hoare (assume (j < length patn);; ret j)
        (fun j' => j' = j /\ jrange j').
Proof.
  intros; unfold jrange; hoare_auto. 
  split; auto; lia.
Qed.

(** Group 2: partial match *)
Notation partial_match i j := 
  (partial_match_res patn (sublist 0 i text) (sublist 0 j patn)). 

Lemma partial_match_init:
  partial_match 0 0.
Proof.
  repeat rewrite sublist_nil; auto.
  apply partial_match_nil.
Qed.

Lemma partial_match_inner_cnt (i j: nat):
  length next <= length patn ->
  prefix_func next ->
  jrange j ->
  partial_match i j ->
  Hoare (assume(j <> 0);; ret (nth (j-1) next 0))
        (fun j' => partial_match i j').
Proof.
  intros Hl Hf Hjr Hp.
  unfold jrange, partial_match in *.
  hoare_auto.
  pose proof (inner_pre_prefix_imply Hf) as Him.
  unfold prefix_func in Hf.
  specialize (Hf (j-1) ltac:(lia)). 
  replace (j - 1 + 1) with j in Hf by lia.
  destruct Hf as [[Hf _] _].
  eapply presuffix_partial_match; eauto.
Qed.

Lemma partial_match_inner_brk1 (i j: nat):
  length next <= length patn ->
  0 <= i < length text ->
  jrange j ->
  partial_match i j ->
  Hoare (assume(nth i text default  = nth j patn default);; ret (j+1))
        (fun j' => partial_match (i+1) j').
Proof.
  intros Hl Hi Hj Hp.
  hoare_auto.
  unfold jrange in Hj.
  rewrite (sublist_one_ele' i _ default) by lia.
  rewrite (sublist_one_ele' j _ default) by lia.
  apply (partial_match_snoc_iff default).
  right; exists (sublist 0 j patn).
  split. apply app_inj_tail_iff; easy.
  pose proof length_sublist 0 j patn ltac:(lia).
  replace (j - 0) with j in H0 by lia.
  split; try lia.
  rewrite H0; split; try easy.
Qed.

Lemma partial_match_inner_brk2 (i j: nat):
  Hoare (assume(j = 0);; ret 0)
        (fun j' => partial_match (i+1) j').
Proof.
  hoare_auto.
  apply partial_match_nil.
Qed.

(** Group 3 partial bound *)
Notation partial_bound i j :=
  (partial_bound_res patn (sublist 0 i text) (sublist 0 j patn)).

Lemma partial_bound_init:
  partial_bound 0 0.
Proof.
  unfold partial_bound.
  intros.
  rewrite sublist_nil in H by lia.
  destruct H as [H _].
  apply suffix_length in H.
  simpl in H; lia.
Qed.

Definition presuffix_inv (i j: nat) :=
  forall k, 0 < k <= length patn ->
    partial_match (i+1) k ->
    (nth (k - 1) patn default = nth i text default /\
    presuffix (sublist 0 (k - 1) patn) (sublist 0 j patn)).

Lemma presuffix_inv_init (i j: nat):
  length next <= length patn ->
  0 <= i < length text ->
  partial_match i j ->
  partial_bound i j ->
  presuffix_inv i j.
Proof.
  intros Hnp Hi Hm Hb.
  unfold presuffix_inv.
  intros k Hk; intros.
  rewrite <- (sublist_one_ele _ _ (nth i text default) default) in H; try lia; auto.
  rewrite partial_match_snoc_iff with (default:=default) in H.
  destruct H.
  {
    pose proof length_sublist 0 k patn ltac:(lia).
    rewrite H in H0.
    simpl in H0; lia.
  }
  destruct H as [res [? [? [? ?]]]].
  pose proof (f_equal (@length _) H) as Hl.
  rewrite length_sublist in Hl by lia.
  rewrite app_length in Hl.
  simpl in Hl.
  assert (k - 1 = length res) by lia.
  split; [rewrite H3; auto | ].
  rewrite <- (partial_match_iff _ _ _ Hm Hb).
  rewrite (sublist_split 0 k (k-1)) in H by lia.
  rewrite (sublist_single' _ _ default) in H by lia.
  rewrite <- H1 in *; rewrite <- H3 in H.
  apply app_inv_tail in H.
  rewrite H; auto.
Qed.


Lemma presuffix_inner_cnt (i j: nat):
  length next <= length patn ->
  prefix_func next ->
  jrange j ->
  presuffix_inv i j ->
  nth i text default <> nth j patn default ->
  Hoare (assume(j <> 0);; ret (nth (j-1) next 0))
        (fun j' => presuffix_inv i j').
Proof.
  intros H Hf H0 Hj Hneq.
  unfold jrange in H0.
  hoare_auto.
  unfold prefix_func in Hf.
  specialize (Hf (j-1) ltac:(lia)). 
  replace (j - 1 + 1) with j in Hf by lia.
  unfold presuffix_inv in *.
  intros k Hk.
  specialize (Hj k Hk).
  intros Hp.
  apply Hj in Hp; clear Hj.
  destruct Hf as [Hfj Hf]. 
  split; try easy.
  destruct Hp as [Hj1 Hj2].
  pose proof (length_sublist 0 (k - 1) patn ltac:(lia)) as Hklen.
  pose proof (length_sublist 0 j patn ltac:(lia)) as Hjlen.
  pose proof presuffix_length _ _ Hj2.
  destruct (j - (k - 1)) eqn:Ej; try lia.
  replace (k - 1) with j in Hj1 by lia.
  rewrite Hj1 in Hneq; easy.
  assert (Hlen: length (sublist 0 (k - 1) patn) < length (sublist 0 j patn)) by lia.
  apply Hf.
  unfold proper_presuffix; tauto.
Qed.

Lemma partial_bound_inner_brk1 (i j: nat):
  length next <= length patn ->
  jrange j ->
  presuffix_inv i j ->
  Hoare (assume(nth i text default = nth j patn default);; 
         ret (j+1))
        (fun j' => partial_bound (i+1) j').
Proof.
  intros Hl Hjr Hp.
  unfold jrange in Hjr.
  hoare_auto.
  intros res Hr.
  pose proof (proj2 Hr) as Hrp.
  apply prefix_iff_sublist in Hrp.
  destruct Hrp as [j0 [Hj ?]]; subst res.
  destruct j0; try lia.
  remember (S j0) as p.
  rewrite length_sublist' in Hj.
  specialize (Hp p ltac:(lia)).
  apply Hp in Hr; clear Hp.
  destruct Hr as [_ Hr].
  apply presuffix_length in Hr.
  repeat rewrite length_sublist in Hr by lia.
  repeat rewrite length_sublist by lia; lia.
Qed.

Lemma partial_bound_inner_brk2 (i j: nat):
  nth i text default <> nth j patn default ->
  presuffix_inv i j ->
  Hoare (assume(j = 0);; ret 0)
        (fun j' => partial_bound (i+1) j').
Proof.
  intros Hneq Hp.
  hoare_auto.
  subst j.
  rewrite (sublist_nil patn) by lia.
  unfold partial_bound_res.
  intros res Hr.
  pose proof (proj2 Hr) as Hrp.
  apply prefix_iff_sublist in Hrp.
  destruct Hrp as [j0 [Hj ?]]; subst res.
  destruct j0; try lia.
  remember (S j0) as p; assert (p > 0) by lia; clear Heqp j0.
  rewrite length_sublist' in Hj.
  unfold presuffix_inv in Hp.
  specialize (Hp p ltac:(lia)).
  apply Hp in Hr.
  destruct Hr as [Hc Hr].
  rewrite (sublist_nil _ 0 0) in Hr by lia.
  apply presuffix_length in Hr.
  rewrite length_sublist in Hr by lia.
  simpl in Hr.
  assert (p = 1) by lia; subst.
  replace (1-1) with 0 in Hc by lia.
  congruence.
Qed.

(** Group 4: post loop*)
Lemma no_occur_init:
  patn <> nil ->
  no_occur 0.
Proof.
  intros.
  apply length_nonnil in H.
  unfold no_occur.
  intros; lia.
Qed.

Lemma no_occur_cnt (i j: nat):
  length next = length patn ->
  0 <= i < length text ->
  jrange j  ->
  partial_bound (i+1) j ->
  no_occur i ->
  no_occur (i+1).
Proof.
  intros Hleq Hi Hjr Hp Hn.
  unfold no_occur in *; intros i0 Hi0.
  unfold jrange in Hjr.
  remember (length patn) as lp.
  destruct (le_gt_dec (i+1-lp) i0).
  2:{ apply Hn; lia. }
  assert (i0 + lp = i + 1) by lia; clear Hi0 l.
  rewrite H.
  intros con. subst lp.
  unfold partial_bound in Hp.
  rewrite (length_sublist _ j) in Hp by lia.
  replace (j-0) with j in Hp by lia.
  assert (length (sublist i0 (i + 1) text) <= j).
  {
    apply Hp.
    split.
    - apply suffix_iff_sublist.
      exists i0.
      repeat rewrite length_sublist by lia.
      replace (i+1-0) with (i+1) by lia.
      split; [lia|].
      rewrite <- (sublist_self text (length text)) at 1 by auto.
      rewrite (sublist_split 0 _ (i+1)) by lia.
      rewrite sublist_split_app_l; auto; [lia|].
      rewrite length_sublist; lia. 
    - rewrite con.
      exists nil; rewrite app_nil_r; auto.    
  }
  rewrite length_sublist in H0 by lia.
  apply (f_equal (@length A)) in con.
  rewrite length_sublist in con; lia.
Qed.

Lemma no_occur_brk (i j: nat):
  partial_match (i+1) j ->
  no_occur i ->
  Hoare (assume (j = length patn);; ret (i + 1 - length patn))
        (fun r => no_occur (r + length patn - 1)).
Proof.
  intros; hoare_auto.
  destruct H as [H _].
  apply suffix_length in H.
  repeat rewrite length_sublist' in H.
  replace (i + 1 - length patn + length patn - 1) with i by lia.
  auto.
Qed.

Lemma first_occur_brk (i j: nat):
  i < length text ->
  partial_match (i+1) j ->
  Hoare (assume (j = length patn);; ret (i + 1 - length patn))
        (fun r => sublist r (r + length patn) text = patn).
Proof.
  intros Hi H; hoare_auto.
  destruct H as [H _].
  subst.
  rewrite sublist_self in H by auto.
  pose proof suffix_length _ _ H as H0.
  rewrite length_sublist in H0 by lia.
  apply suffix_iff_sublist in H.
  destruct H as [i0 [H H1]].
  rewrite length_sublist in H by lia.
  replace (i+1-0) with (i+1) in H by lia.
  rewrite <- H.
  rewrite length_sublist in H1 by lia.
  replace (i+1-0) with (i0 + length patn) in H1 by lia.
  rewrite H1 at 2.
  rewrite <- (sublist_self text (length text)) at 1 by auto.
  rewrite (sublist_split 0 _ (i + 1)) by lia.
  rewrite sublist_split_app_l; auto; [lia|].
  rewrite length_sublist; lia.  
Qed.

(** Stage 2: Mechanized Proof *)

(** We only include props containing parameter variables i and j *)
Definition match_inv (i j: nat) :=
  jrange j /\
  partial_match i j /\
  partial_bound i j /\
  no_occur i.

Definition inner_inv (i j: nat) :=
  jrange j /\
  partial_match i j /\
  presuffix_inv i j.

Definition inner_post (i j: nat) :=
  0 <= j <= length next /\
  partial_match (i+1) j /\
  partial_bound (i+1) j.

Lemma inner_cnt_prop (i j: nat):
  length next <= length patn ->
  prefix_func next ->
  (forall k, jrange k -> 0 <= nth k next 0 <= k) ->
  inner_inv i j ->
  Hoare (x <- inner_body default patn next (nth i text default) j;; 
              continue_case x)
        (fun j' => inner_inv i j').
Proof.
  unfold inner_inv; intros.
  apply Hoare_conj.
  apply inner_range_cnt; tauto.
  unfold inner_body.
  hoare_step. hoare_auto.
  do 2 hoare_step. hoare_auto.
  hoare_conj.
  - hoare_apply partial_match_inner_cnt.
  - hoare_apply presuffix_inner_cnt.
Qed.

Lemma inner_brk_prop (i j: nat):
  length next <= length patn ->
  prefix_func next ->
  0 <= i < length text ->
  inner_inv i j ->
  Hoare (x <- inner_body default patn next (nth i text default) j;; 
              break_case x)
        (fun j' => inner_post i j').
Proof.
  unfold inner_inv, inner_post; intros.
  apply Hoare_conj.
  apply inner_range_brk; tauto.
  unfold inner_body; hoare_step.
  - hoare_conj.
    + hoare_apply partial_match_inner_brk1.
    + hoare_apply partial_bound_inner_brk1.
  - do 2 hoare_step; [|hoare_auto]. 
    hoare_conj.
    + hoare_apply partial_match_inner_brk2.
    + hoare_apply partial_bound_inner_brk2.
Qed.

(** This inner prop is for both match and constr procedures *)
Lemma inner_loop_prop (i j: nat):
  length next <= length patn ->
  prefix_func next ->
  0 <= i < length text ->
  jrange j ->
  partial_match i j ->
  partial_bound i j ->
  Hoare (inner_loop default patn next (nth i text default) j)
        (fun j' => inner_post i j').
Proof.
  intros.
  apply Hoare_repeat_break with (P:= inner_inv i).
  - intros.
    apply inner_cnt_prop; auto.
    apply inner_pre_prefix_imply; auto.
  - intros.
    apply inner_brk_prop; auto.
  - unfold inner_inv.
    split; [tauto| split]; [tauto|].
    apply presuffix_inv_init; auto.
Qed.

Lemma match_cnt_prop (i j: nat):
  length next = length patn ->
  prefix_func next ->
  0 <= i < length text ->
  match_inv i j ->
  Hoare (x <- match_body default patn text next (i, j);; 
              continue_case x)
        (fun r => match_inv (i+1) r).
Proof.
  unfold match_inv; intros.
  unfold match_body.
  monad_law.
  hoare_post inner_loop_prop; try tauto; try lia.
  unfold inner_post in H3.
  hoare_step; [hoare_auto|].
  eapply Hoare_conseq.
  2:{ hoare_apply match_range_cnt. }
  simpl; intros.
  destruct H4; subst a0.
  split; auto.
  split; [tauto|].
  split; [tauto|].
  apply no_occur_cnt with (j:=a); tauto.
Qed.
  
Lemma match_brk_prop (i j: nat):
  length next = length patn ->
  prefix_func next ->
  0 <= i < length text ->
  match_inv i j ->
  Hoare (x <- match_body default patn text next (i, j);; 
              break_case x)
        first_occur.
Proof.
  unfold match_inv; intros.
  unfold match_body.
  monad_law.
  hoare_post inner_loop_prop; try tauto; try lia.
  unfold inner_post in H3.
  hoare_step; [|hoare_auto].
  unfold first_occur; hoare_conj.
  - hoare_apply first_occur_brk.
  - hoare_apply no_occur_brk.
Qed.

Theorem match_loop_sound:
  match_pre ->
  Hoare (match_loop default patn text next)
         match_post.
Proof.
  unfold match_pre, match_post, match_loop; intros.
  eapply Hoare_conseq.
  2:{
    apply Hoare_range_iter_break with (P:= fun '(i, j) => match_inv i j).
    - lia.
    - intros; apply match_cnt_prop; tauto.
    - intros; apply match_brk_prop; tauto.
    - unfold match_inv.
      split; [apply jrange_init; tauto|].
      split; [apply partial_match_init|].
      split; [apply partial_bound_init|].
      apply no_occur_init; tauto.
  }
  simpl; intros.
  destruct a; auto.
  unfold match_inv in H0; tauto.
Qed.

End match_proof.

Section constr_proof.
Context {A: Type}
        (default: A)
        (patn: list A).

(** Goal of proof:
    Pre: patn <> nil
    Post: fun next =>
          prefix_func next /\
          length next = length patn
*)

(** It's a natural idea to prove by showing that the constr_loop 
    builds a correct prefix_func table with length `i` increasing.
    The role of `j` should also be an invariant. 
*)
Definition constr_inv (i j: nat) (next: list nat) :=
  prefix_func patn next /\
  i = length next /\
  j = nth (i-1) next 0.

Definition constr_inv_init:
  patn <> nil ->
  constr_inv 1 0 [0].
Proof.
  intros; unfold constr_inv.
  apply length_nonnil in H.
  simpl.
  split; [| lia].
  unfold prefix_func; intros.
  simpl in H0.
  assert (i0 = 0) by lia; subst i0; simpl.
  split; hnf.
  - rewrite sublist_nil by auto.
    split; [apply nil_presuffix|].
    rewrite length_sublist by lia.
    simpl; lia.
  - intros.
    rewrite sublist_nil by lia.
    destruct H1 as [_ H1].
    rewrite length_sublist in H1 by lia.
    assert (length l3 = 0) by lia.
    apply length_zero_iff_nil in H2.
    subst; apply nil_presuffix.
Qed.

(** Spec derivation for inner_loop 
    with text:= patn[1..patn.len] and i:= i-1
    since patn[i] = patn[1..patn.len][i-1].
*)

Notation partial_match' i j :=
  (partial_match_res patn (sublist 1 i patn) (sublist 0 j patn)).

Notation partial_bound' i j :=
  (partial_bound_res patn (sublist 1 i patn) (sublist 0 j patn)).


Lemma constr_prefunc_imply (i j: nat) (next: list nat):
  1 <= i < length patn ->
  constr_inv i j next ->
  proper_presuffix (sublist 0 j patn) (sublist 0 i patn) /\
  presuffix_bound (sublist 0 j patn) (sublist 0 i patn).
Proof.
  intros Hir (Hp & Hi & Hj).
  specialize (Hp (i-1) ltac:(lia)).
  replace (i-1+1) with i in Hp by lia.
  rewrite <- Hj in Hp.
  tauto.
Qed.

Lemma constr_inner_pre_range (i j: nat) (next: list nat):
  1 <= i < length patn ->
  constr_inv i j next ->
  jrange next j.
Proof.
  unfold constr_inv; intros Hir (Hp & Hi & Hj).
  unfold jrange; rewrite <- Hi.
  apply inner_pre_prefix_imply with (k:=(i-1))in Hp.
  lia.
  unfold jrange; lia.
Qed.

Lemma constr_inner_pre_match (i j: nat) (next: list nat):
  1 <= i < length patn ->
  proper_presuffix (sublist 0 j patn) (sublist 0 i patn) ->
  partial_match' i j.
Proof.
  intros Hir ((Hp & Hs) & Hl).
  remember (sublist 0 j patn) as lj.
  rewrite length_sublist in Hl; try lia.
  rewrite Nat.sub_0_r in Hl.
  split.
  - apply suffix_sublist_cons_iff; try lia.
    split; [lia | auto].
  - apply prefix_sublist_iff in Hp; [easy | lia].
Qed.

Lemma constr_inner_pre_bound (i j: nat) (next: list nat):
  1 <= i < length patn ->
  presuffix_bound (sublist 0 j patn) (sublist 0 i patn) ->
  partial_bound' i j.
Proof.
  unfold presuffix_bound, partial_bound'; intros Hir Hb.
  remember (sublist 0 j patn) as lj.
  intros res (Hs & Hp).
  apply presuffix_length.
  apply Hb.
  pose proof suffix_length _ _ Hs.
  rewrite length_sublist in H by lia.
  split; [split | ].
  apply prefix_sublist_iff; try lia.
  split; [lia | auto].
  apply suffix_sublist_cons_iff; [lia | easy].
  rewrite length_sublist by lia. lia.
Qed.

Lemma sublist_skip1_eq (i:nat):
  1 <= i <= length patn ->
  sublist 1 i patn = sublist 0 (i-1) (skipn 1 patn).
Proof.
  intros.
  unfold sublist.
  repeat rewrite skipn_firstn.
  rewrite skipn_O.
  rewrite Nat.sub_0_r.
  reflexivity.
Qed.

Lemma nth_skip1_eq (i:nat):
  1 <= i < length patn ->
  nth i patn default = nth (i-1) (skipn 1 patn) default.
Proof.
  intros.
  rewrite nth_skipn.
  replace (i-1+1) with i by lia.
  reflexivity.
Qed.

(** Now we show that after inner_loop, the invariants are kept. *)
Lemma constr_inner_post_match (i j: nat):
  1 <= i < length patn ->
  partial_match' (i+1) j ->
  proper_presuffix (sublist 0 j patn) (sublist 0 (i+1) patn).
Proof.
  intros Hir (Hs & Hp).
  unfold proper_presuffix.
  pose proof suffix_length _ _ Hs.
  remember (sublist 0 j patn) as lj.
  rewrite length_sublist in H by lia.
  split; [split |].
  - apply prefix_sublist_iff; try lia.
    split; [lia | auto].
  - apply suffix_sublist_cons_iff in Hs; [tauto | lia].
  - rewrite length_sublist by lia; lia.
Qed.

Lemma constr_inner_post_bound (i j: nat):
  1 <= i < length patn ->
  partial_match' (i+1) j ->
  partial_bound' (i+1) j ->
  presuffix_bound (sublist 0 j patn) (sublist 0 (i+1) patn).
Proof.
  intros Hir (Hs & Hp) Hb.
  hnf; hnf in Hb.
  intros l [[Hpl Hsl] Hl].
  pose proof suffix_length _ _ Hs.
  remember (sublist 0 j patn) as lj.
  rewrite length_sublist in H, Hl by lia.
  assert (length l <= length lj).
  {
    apply Hb; split.
    apply suffix_sublist_cons_iff; try lia.
    split; [lia | auto].
    apply prefix_sublist_iff in Hpl; try lia; tauto.
  }
  clear Hb; split.
  apply prefix_sublist_iff in Hpl; try lia.
  apply (prefix_total_order _ _ patn); tauto.
  apply suffix_total_order with (l:=(sublist 1 (i+1) patn)); try tauto.
  apply suffix_sublist_cons_iff; try lia.
  split; auto; lia.
Qed.

Lemma prefix_func_inv (i j: nat) (next: list nat):
  1 <= i < length patn ->
  i = length next ->
  proper_presuffix (sublist 0 j patn) (sublist 0 (i+1) patn) ->
  presuffix_bound (sublist 0 j patn) (sublist 0 (i+1) patn) ->
  prefix_func patn next ->
  prefix_func patn (next ++ [j]).
Proof.
  intros Hir Hi Hpp Hb Hpf.
  unfold prefix_func in *.
  intros k Hk.
  rewrite app_length in Hk; simpl in Hk.
  destruct (Nat.eq_dec k i).
  2:{
    rewrite app_nth1 by lia.
    apply Hpf; lia. 
  }
  subst k; clear Hk.
  hnf.
  rewrite app_nth2 by lia.
  replace (i - length next) with 0 by lia.
  simpl; tauto.
Qed.

(** Now we can do the mechanized proof *)
Lemma constr_body_prop (i j: nat) (next: list nat):
  1 <= i < length patn ->
  constr_inv i j next ->
  Hoare (constr_body default patn (i, (next, j)))
        (fun '(next', j') => constr_inv (i+1) j' next').
Proof.
  unfold constr_inv; intros Hir Hp.
  pose proof (constr_prefunc_imply _ _ _ Hir Hp). 
  unfold constr_body.
  rewrite nth_skip1_eq by lia.
  hoare_post (inner_loop_prop _ _ (skipn 1 patn) _ (i-1)); try tauto; try lia.
  - rewrite skipn_length; lia.
  - apply (constr_inner_pre_range i); auto.
  - rewrite <- sublist_skip1_eq by lia. 
    apply constr_inner_pre_match; tauto.
  - rewrite <- sublist_skip1_eq by lia.
    apply constr_inner_pre_bound; tauto.
  - unfold inner_post in H0.
    replace (i-1+1) with (i+1-1) in H0 by lia.
    rewrite <- sublist_skip1_eq in H0 by lia.
    hoare_auto.
    split; [|split].
    + eapply prefix_func_inv; eauto; try tauto.
      apply constr_inner_post_match; tauto.
      apply constr_inner_post_bound; tauto.
    + rewrite app_length; simpl; lia.
    + rewrite app_nth2 by lia.
      replace (i + 1 - 1 -length next) with 0 by lia.
      reflexivity.
Qed.

Theorem constr_loop_sound:
  patn <> nil ->
  Hoare (contsr_loop default patn)
        (fun next => prefix_func patn next /\ length next = length patn).
Proof.
  intros.
  pose proof (length_nonnil _ H).
  unfold contsr_loop.
  eapply Hoare_bind.
  - apply Hoare_range_iter with (P:= fun '(i, (next, j)) => constr_inv i j next).
    + lia.
    + intros. 
      destruct a. 
      apply constr_body_prop; auto.
    + apply constr_inv_init; auto.
  - intros.
    destruct a as [next j].
    hoare_auto.
    unfold constr_inv in H1; easy.
Qed.

End constr_proof.
