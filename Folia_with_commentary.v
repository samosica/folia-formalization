(******************************************************************************)
(* A formalization of Folia                                                   *)
(*   Folia is a problem in a competitive programming contest, NOMURA          *)
(* programming contest 2020. The problem is described as follows [1]:         *)
(*                                                                            *)
(* ``` (the beginning of a quote)                                             *)
(* Given is an integer sequence of length N + 1: A[0], A[1], A[2], ..., A[N]. *)
(* Is there a binary tree of depth N such that, for each d = 0, 1, ..., N,    *)
(* there are exactly A[d] leaves at depth d? If such a tree exists, print the *)
(* maximum possible number of vertices in such a tree; otherwise, print −1.   *)
(* ``` (the end)                                                              *)
(*                                                                            *)
(*   This file extends the problem in the following way:                      *)
(* - Besides the maximum possible number, compute the minimum possible number *)
(* - Replace "a binary tree" in the above statement with a set of n binary    *)
(*   trees (a forest); the generalization naturally arises in ensuring the    *)
(*   correctness of a solution for the original version. Suppose that you     *)
(*   prove its correctness by structural induction on the sequence [A[0], ... *)
(*   A[N]]. In this case, the induction hypothesis gives information on all   *)
(*   nodes in a tree except the root, in other words, the second layer (depth *)
(*   2) and the lower layers. Since removing the root from a tree may create  *)
(*   some trees but not a single tree, it is necessary to extend the problem  *)
(*   to forests.                                                              *)
(* Then this file verifies the extended version as follows:                   *)
(* 1. Define functions computing a bound (lb, ub) (a pair of a lower bound    *)
(*    and an upper bound) of the size of forests satisfying the condition on  *)
(*    leaves. These functions ignore the condition on the size of forests.    *)
(* 2. Prove that there exists a forest of size n with the desired property if *)
(*    and only if lb <= n <= ub, which shows that (lb, ub) is a tight bound.  *)
(* 3. Define functions computing a bound (lb', ub') of the total numbers of   *)
(*    nodes in forests consisting n trees and satisfying the condition on     *)
(*    leaves.                                                                 *)
(* 4. Prove that there exists a forest that has n trees and m nodes in total  *)
(*    if and only if lb <= n <= ub and lb' <= m <= ub', which shows that      *)
(*    (lb', ub') is a tight bound.                                            *)
(* 5. Define functions that are equivalent to the ones described in (1) but   *)
(*    are efficiently computed.                                               *)
(*                                                                            *)
(*   As a result, we can solve the problem in the following way:              *)
(* 1. Calculate lb and ub                                                     *)
(* 2. Check if lb <= n <= ub. If so, go to (3); otherwise print -1            *)
(* 3. Calculate lb' and ub' and print them                                    *)
(*                                                                            *)
(* References:                                                                *)
(* [1] https://atcoder.jp/contests/nomura2020/tasks/nomura2020_c              *)
(*                                                                            *)
(* Binary trees and their forests                                             *)
(*             bintree := a binary tree                                       *)
(*              forest := a sequence of trees                                 *)
(*        count_node t := the number of nodes on a tree t                     *)
(* count_node_forest f := the number of nodes on a forest f                   *)
(*          subtrees t := trees just below the root of a tree t               *)
(*         subforest f := subtrees of trees in a forest f                     *)
(*                                                                            *)
(* Specifications of leaves:                                                  *)
(*             leave_spec := a sequence specifying the number of leaves at    *)
(*                           each level in a forest                           *)
(* satisfy_leave_spec f s := check whether a forest f satisfies a spec s      *)
(*                           (for a tree t, use satisfy_leave_spec [:: t] s)  *)
(*                                                                            *)
(* Forest lifts:                                                              *)
(*    simple_lift f : adds one node on to the top of each tree in a forest f  *)
(* pairing_lift p f : divides trees in a forest f into p pairs and other      *)
(*                    individuals, and adds one node on to the top of each    *)
(*                    group                                                   *)
(*                                                                            *)
(* Bounds:                                                                    *)
(*     lower_bound_bottomup s, : a tight bound of the size of forests that    *)
(*     upper_bound_bottomup s    satisfy a spec s; see in_bottomup_boundP     *)
(* lower_bounds_backforth s n, : tight bounds of the number of nodes at all   *)
(* upper_bounds_backforth s n    levels of forests consisting n trees and     *)
(*                               satisfying a spec s                          *)
(*      lower_bound_total s n, : a tight bound of the total numbers of nodes  *)
(*      upper_bound_total s n    in forests consisting n trees and satisfying *)
(*                               a spec s; see in_total_boundP                *)
(*                                                                            *)
(* Efficiently computed bounds:                                               *)
(*    lower_bounds_topdown s n, : bounds of the number of nodes at all levels *)
(*    upper_bounds_topdown s n    of forests consisting n trees and           *)
(*                                satisfying a spec s; they may not be tight  *)
(* lower_bounds_backforth' s n, : the same as lower/upper_bound_backforth     *)
(* upper_bounds_backforth' s n                                                *)
(*      lower_bound_total' s n, : the same as lower/upper_bound_total; the    *)
(*      upper_bound_total' s n    time complexity is Θ(|s|) (|s| is the size  *)
(*                                of s)                                       *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq Require Import Lia.
From mathcomp.zify Require Import zify.

Section SsrnatExt.
Lemma leq_div2 n : n./2 <= n.
Proof. by rewrite -divn2 leq_div. Qed.

Lemma leq_uphalf n : uphalf n <= n.
Proof.
  (* TODO: Use leqRHS instead of [in X in _ <= X] in the later versions of MathComp 1.15.0 *)
  rewrite [in X in _ <= X](divn_eq n 2) addnC uphalf_half -modn2 -divn2.
  by apply: leq_add => //; apply: leq_pmulr.
Qed.

(* Note: homo_maxl can be generalized as follows: if a <= b and c <= d, then  *)
(* maxn a c <= maxn b d                                                       *)
Lemma homo_maxl n :
  {homo maxn n : m l / m <= l}.
Proof.
  move=> m l leq_ml.
  by rewrite geq_max leq_maxl leq_max leq_ml orbT.
Qed.

Lemma homo_minl n :
  {homo minn n : m l / m <= l}.
Proof.
  move=> m l leq_ml.
  by rewrite leq_min geq_minl geq_min leq_ml orbT.
Qed.
End SsrnatExt.

Section SeqExt.
Lemma flatten_nseq_nil (T : Type) (n : nat) :
  @flatten T (nseq n [::]) = [::].
Proof. by elim: n. Qed.

Section Map.
  Variable A B C : Type.

  (* Note: [map2] is defined by fix, instead of Fixpoint, to exclude [f] from the recursive definition *)
  Definition map2 (f : A -> B -> C) :=
    fix map2 (s1 : seq A) (s2 : seq B) :=
      match s1, s2 with
        x :: s1', y :: s2' => f x y :: map2 s1' s2'
      | _, _ => [::]
      end.
End Map.

Section Scan.
Variable T S : Type.
Variable f : T -> S -> S.
Variable y0 : S.

(* Note: scanr_aux corresponds to scanr in Haskell, although the former       *)
(* definition is rather complicated than the latter one. In Coq, partial      *)
(* functions are rejected so it is required to guarantee that scanr_aux does  *)
(* not return the empty sequence.                                             *)
Fixpoint scanr_aux (s : seq T) : {r : seq S | size r > 0} :=
  match s with
    [::] => exist _ [:: y0] erefl
  | x :: s' =>
      match scanr_aux s' with
        exist r Hr =>
          (match r return size r > 0 -> {r : seq S | size r > 0} with
             [::] => fun cont => match notF cont with end
           | y :: _ => fun Hr => exist _ (f x y :: r) erefl
           end) Hr
      end
  end.

Lemma scanr_auxE (x : T) (s' : seq T) :
  scanr_aux (x :: s') =
    match scanr_aux s' with
      exist r Hr =>
        (match r return size r > 0 -> {r : seq S | size r > 0} with
           [::] => fun cont => match notF cont with end
         | y :: _ => fun Hr => exist _ (f x y :: r) erefl
         end) Hr
    end.
Proof. by []. Qed.

Definition scanr (s : seq T) := proj1_sig (scanr_aux s).

Lemma scanrE (x : T) (s : seq T) :
  scanr (x :: s) = foldr f y0 (x :: s) :: scanr s.
Proof.
  rewrite /scanr.
  elim: s => // x' s' IH in x *.
  rewrite scanr_auxE.
  case: (scanr_aux (x' :: s')) (IH x') => /= r Hr Er.
  rewrite Er /= in Hr *.
  by congr (_ :: _).
Qed.
End Scan.
End SeqExt.

Section BinaryTree.
Inductive bintree := L | B1 of bintree | B2 of bintree & bintree.
Definition forest := seq bintree.

Fixpoint bintree_eq (t1 t2 : bintree) :=  
  match t1, t2 with
  | L, L => true
  | B1 t1', B1 t2' => bintree_eq t1' t2'
  | B2 t11 t12, B2 t21 t22 => bintree_eq t11 t21 && bintree_eq t12 t22
  | _, _ => false
  end.

Lemma bintree_eqP : Equality.axiom bintree_eq.
Proof.
move=> t1 t2; apply/(iffP idP).
- elim: t1 t2 => [| t1' IH | t11 IH1 t12 IH2].
  + by case.
  + by case => //= t2' E; congr B1; apply: IH.
  + by case => //= t21 t22 /andP [E1 E2]; congr B2; [ apply: IH1 | apply: IH2 ].
- by move<-; elim: t1 => //= t11 IH1 t12 IH2; rewrite IH1 IH2.
Qed.

Canonical bintree_eqMixin := EqMixin bintree_eqP.
Canonical bintree_eqType := Eval hnf in EqType bintree bintree_eqMixin.

Fixpoint count_node (t : bintree) :=
  match t with
    L => 1
  | B1 t1 => (count_node t1).+1
  | B2 t1 t2 => (count_node t1 + count_node t2).+1
  end.

Definition count_node_forest (f : forest) :=
  sumn (map count_node f).

Lemma count_node_forest_cat (f1 f2 : forest) :
  count_node_forest (f1 ++ f2) = count_node_forest f1 + count_node_forest f2.
Proof. by rewrite /count_node_forest map_cat sumn_cat. Qed.

Lemma count_node_forest_nseq n t :
  count_node_forest (nseq n t) = (count_node t) * n.
Proof. by rewrite /count_node_forest map_nseq sumn_nseq. Qed.

Definition subtrees (t : bintree) : forest :=
  match t with
    L => [::]
  | B1 t => [:: t]
  | B2 t1 t2 => [:: t1; t2]
  end.

Definition subforest (f : forest) : forest :=
  flatten (map subtrees f).

Lemma subforest_cat f1 f2 :
  subforest (f1 ++ f2) = subforest f1 ++ subforest f2.
Proof. by rewrite /subforest map_cat flatten_cat. Qed.

Lemma subforest_nseq n t :
  subforest (nseq n t) = flatten (nseq n (subtrees t)).
Proof. by rewrite /subforest map_nseq. Qed.

Lemma eq_count_node t :
  count_node t = (count_node_forest (subtrees t)).+1.
Proof.
  rewrite /count_node_forest.
  by case: t => //= [t1 | t1 t2]; rewrite addn0.
Qed.

Lemma eq_count_node_forest f :
  count_node_forest f = size f + count_node_forest (subforest f).
Proof.
  rewrite /count_node_forest /subforest.
  elim: f => //= t0 f' IH.
  rewrite map_cat sumn_cat.
  (* Note: addn.[AC (2*2) ((3*2)*(1*4))] replaces a term like (a + b) + (c + d) *)
  (* with (c + b) + (a + d). In general, MathComp provides a handy tool to      *)
  (* rewrite terms built by an operation using its commutativity and its        *)
  (* associativity; see ssrAC.v in MathComp.                                    *)
  rewrite -addn1 addn.[AC (2*2) ((3*2)*(1*4))] addn1.
  congr (_ + _) => //.
  by apply: eq_count_node.
Qed.
End BinaryTree.

Section LeaveSpec.
Definition leave_spec := seq nat.

Fixpoint satisfy_leave_spec (f : forest) (s : leave_spec) :=
  match s with
    [::] => f == [::]
  | l0 :: s' =>
      let f' := subforest f in
      (count_mem L f == l0) && satisfy_leave_spec f' s'
  end.
End LeaveSpec.

(******************************************************************************)
(* Step 1: Compute a bound of the size of forests                             *)
(******************************************************************************)

Definition lower_bound_bottomup (s : leave_spec) :=
  foldr (fun l0 lb => l0 + uphalf lb) 0 s.

Definition upper_bound_bottomup (s : leave_spec) :=
  foldr (fun l0 ub => l0 + ub) 0 s.

Lemma leq_bottomup_bound (s : leave_spec) :
  lower_bound_bottomup s <= upper_bound_bottomup s.
Proof.
  elim: s => //= l0 s' IH.
  by rewrite leq_add2l (leq_trans _ IH) ?leq_uphalf.
Qed.

Section ForestLift.
Definition simple_lift (f : forest) := map B1 f.

Fixpoint pairing_lift (p : nat) (f : forest) :=
  match p, f with
    p'.+1, t0 :: t1 :: f' => B2 t0 t1 :: pairing_lift p' f'
  | _, _ => simple_lift f
  end.

Lemma subforest_simple_lift f :
  subforest (simple_lift f) = f.
Proof.
  rewrite /subforest.
  elim: f => //= t0 f' IH.
  by congr (_ :: _).
Qed.

Lemma subforest_pairing_lift p f :
  subforest (pairing_lift p f) = f.
Proof.
  rewrite /subforest.
  elim: p f => [| p' IH]; first by apply: subforest_simple_lift.
  case => [| t0 [| t1 f']] //=.
  by congr (_ :: _ :: _).
Qed.

Lemma size_simple_lift f :
  size (simple_lift f) = size f.
Proof. by rewrite size_map. Qed.

Lemma size_pairing_lift p f :
  p <= half (size f) ->
  size (pairing_lift p f) = size f - p.
Proof.
  elim: p => [| p' IH] in f *.
  - by rewrite subn0 size_simple_lift.
  - case: f => [| t0 [| t1 f']] //= /[!ltnS] ltn_p'.
    rewrite subSS subSn; last first.
    + by apply/(leq_trans ltn_p')/leq_div2.
    + by congr _.+1; apply: IH.
Qed.

Lemma count_mem_L_simple_lift f :
  count_mem L (simple_lift f) = 0.
Proof. by rewrite count_map count_pred0. Qed.

Lemma count_mem_L_pairing_lift p f :
  count_mem L (pairing_lift p f) = 0.
Proof.
  elim: p => [| p' IH] in f *; first by rewrite count_mem_L_simple_lift.
  case: f => [| t0 [| t1 f']] //=.
  by rewrite add0n.
Qed.

Lemma count_node_forest_pairing_lift p f :
  p <= half (size f) ->
  count_node_forest (pairing_lift p f) = count_node_forest f + (size f - p).
Proof.
  move=> ltn_p.
  rewrite eq_count_node_forest.
  by rewrite size_pairing_lift // subforest_pairing_lift addnC.
Qed.
End ForestLift.

Lemma in_size_forest f :
  count_mem L f + uphalf (size (subforest f)) <= size f <= count_mem L f + size (subforest f).
Proof.
  rewrite /subforest.
  elim: f => // t0 f' IH.
  case: t0 => [| t0' | t01 t02] /=.
  - by rewrite add1n !addSn ltnS.
  - case/andP: IH => IHlb IHub.
    rewrite add0n !addnS !ltnS; apply/andP; split => //.
    by rewrite (leq_trans _ IHlb) ?leq_add2l ?uphalf_half ?leq_addl.
  - case/andP: IH => IHlb IHub.
    rewrite add0n !addnS !ltnS; apply/andP; split => //.
    by rewrite (leq_trans IHub).
Qed.

(******************************************************************************)
(* Step 2: Prove the existence of a forest whose size is included in the      *)
(*         bound defined in Step 1                                            *)
(******************************************************************************)

Proposition in_bottomup_boundP (n : nat) (s : leave_spec) :
  reflect (exists2 f, size f = n & satisfy_leave_spec f s) (lower_bound_bottomup s <= n <= upper_bound_bottomup s).
Proof.
  apply: (iffP idP).
  - elim: s => [| l0 s' IH] /= in n *.
    + by rewrite leqn0 => /eqP ->; exists [::].
    + move=> ineq_n.
      set lbb' := lower_bound_bottomup s'.
      set ubb' := upper_bound_bottomup s'.
      (* the number of internal nodes on the top *)
      set i0 := n - l0.
      case: (leqP lbb' i0).
      * (* The case where lbb' <= i0:                                                 *)
        (*   Since lbb' <= i0 <= ubb', using the induction hypothesis, we obtain a    *)
        (* forest f' of size i0 satisfying the spec s'. We can construct a desired    *)
        (* forest from f' by adding one node on to the top of each tree in f' and     *)
        (* creating l0 roots. The total number of trees is i0 + l0 = n.               *)
        move=> le_lbb'_i0.
        have ineq_i0 : lbb' <= i0 <= ubb' by lia.
        case: (IH _ ineq_i0) => f' eq_size_f' sat_f'.
        exists (simple_lift f' ++ nseq l0 L).
        -- by rewrite size_cat size_simple_lift eq_size_f' size_nseq; lia.
        -- apply/andP; split.
           ++ by rewrite count_cat count_mem_L_simple_lift count_nseq mul1n.
           ++ rewrite subforest_cat subforest_simple_lift.
              by rewrite subforest_nseq flatten_nseq_nil cats0.
      * (* The case where i0 < lbb':                                                  *)
        (*   Since lbb' <= lbb' <= ubb', using the induction hypothesis, we obtain a  *)
        (* forest f' of size lbb' satisfying the spec s'. Combining trees in f', we   *)
        (* can make at most floor(lbb' / 2) pairs. By the hypothesis on n, we obtain  *)
        (* the inequality lbb' - i0 <= floor(lbb' / 2). Hence we can make lbb' - i0   *)
        (* pairs. Using them, we construct a desired forest. We first connect each    *)
        (* pair with one node, then, for the remaining trees, add one node on to the  *)
        (* top of each tree. Finally, we create l0 roots. The size of the resulting   *)
        (* forest is (lbb' - i0) + (lbb' - 2 * (lbb' - i0)) + l0 = n.                 *)
        move=> lt_i0_lbb'.
        have ? := leq_bottomup_bound s'.
        have ineq_lbb' : lbb' <= lbb' <= ubb' by lia.
        case: (IH _ ineq_lbb') => f' eq_size_f' sat_f'.
        exists (pairing_lift (lbb' - i0) f' ++ nseq l0 L).
        -- by rewrite size_cat size_pairing_lift ?eq_size_f' ?size_nseq; lia.
        -- apply/andP; split. 
           ++ by rewrite count_cat count_mem_L_pairing_lift count_nseq mul1n.
           ++ rewrite subforest_cat subforest_pairing_lift.
              by rewrite subforest_nseq flatten_nseq_nil cats0.
  - elim: s => [| l0 s' IH] in n *.
    + by case; case; case: n. (* :) *)
    + set lbb' := lower_bound_bottomup s'.
      set ubb' := upper_bound_bottomup s'.
      case => f Esize /= /andP [/eqP EcountL sat].
      have /[!Esize] /[!EcountL] := in_size_forest f.
      have : lbb' <= size (subforest f) <= ubb'.
      { by apply: IH; exists (subforest f). }
      by lia.
Qed.

(******************************************************************************)
(* Step 3: Define a bound of the number of nodes                              *)
(******************************************************************************)

Fixpoint lower_bounds_backforth (s : leave_spec) (n : nat) :=
  match s with
    [::] => [::]
  | l0 :: s' =>
      n :: lower_bounds_backforth s' (maxn (lower_bound_bottomup s') (n - l0))
  end.

Fixpoint upper_bounds_backforth (s : leave_spec) (n : nat) :=
  match s with
    [::] => [::]
  | l0 :: s' =>
      n :: upper_bounds_backforth s' (minn (upper_bound_bottomup s') (n - l0).*2)
  end.

(* N.B. lower/upper_bounds_total are slow. The time complexity is Θ(|s|^2).   *)
(* We will define the faster version in Step 5; see lower/upper_bound_total'. *)
Definition lower_bound_total s n :=
  sumn (lower_bounds_backforth s n).

Definition upper_bound_total s n :=
  sumn (upper_bounds_backforth s n).

Lemma homo_lower_bound_total s :
  {homo lower_bound_total s : n m / n <= m}.
Proof.
  rewrite /lower_bound_total.
  elim: s => //= l0 s' IH n m leq_nm.
  by apply/leq_add => //; apply/IH/homo_maxl/leq_sub2r.
Qed.

Lemma homo_upper_bound_total s :
  {homo (upper_bound_total s) : n m / n <= m}.
Proof.
  rewrite /upper_bound_total.
  elim: s => //= l0 s' IH n m leq_nm.
  apply/leq_add => //; apply/IH.
  by rewrite homo_minl ?leq_double ?leq_sub2r.
Qed.

Lemma leq_total_bound s n m :
  [&& lower_bound_bottomup s <= n, n <= m & m <= upper_bound_bottomup s] ->
  lower_bound_total s n <= upper_bound_total s m.
Proof.
  rewrite /lower_bound_total /upper_bound_total.
  elim: s => //= l0 s' IH in n m *.
  move=> ineq_nm.
  apply: leq_add; first by lia.
  by apply: IH; move: (leq_bottomup_bound s'); lia.
Qed.

(* The lemma below shows that the closed intervals of the form                *)
(*   [lower_bound_total s n, upper_bound_total s n]                           *)
(*   (lower_bound_bottomup s <= n <= upper_bound_bottomup s)                  *)
(* can be depicted as follows (double-headed arrows represent intervals):     *)
(*                                                                            *)
(*              1st: <-------->                                               *)
(*              2nd:       <------>                                           *)
(*              3rd:            <------->                                     *)
(*                                    <--- ........ --->                      *)
(* the last but one:                                  <---->                  *)
(*         the last:                                      <------>            *)
(*                                                                            *)
(* This picture tells us that they cover the closed interval                  *)
(*   [lower_bound_total s (lower_bound_bottomup s),                           *)
(*    upper_bound_total s (upper_bound_bottomup s)].                          *)
Lemma consecutive_total_bounds_touch_each_other s n :
  lower_bound_bottomup s <= n ->
  n.+1 <= upper_bound_bottomup s ->
  lower_bound_total s n <= lower_bound_total s n.+1 <= (upper_bound_total s n).+1.
Proof.
  rewrite /lower_bound_total /upper_bound_total.
  case: s => //= l0 s' in n *.
  move=> geq_n leq_n1.
  apply/andP; split.
  - rewrite ltnW // addSn ltnS leq_add2l homo_lower_bound_total //.
    by lia.
  - rewrite addSn ltnS leq_add2l.
    apply: leq_total_bound.
    apply/and3P; split; [ apply: leq_maxl | | apply: geq_minl ].
    have := leq_bottomup_bound s'.
    suff : 1 <= n - l0 by lia.
    rewrite ltnNge.
    apply/negP => leq_nl0.
    have : upper_bound_bottomup s' > 0 by lia.
    apply/negP.
    rewrite -leqNgt leqn0.
    have : lower_bound_bottomup s' == 0 by lia.
    elim: s' {l0 n geq_n leq_n1 leq_nl0} => //= l1 s'' IH.
    by lia.
Qed.

Lemma interval_chain_forms_closed_interval (f g : nat -> nat) (a b n : nat) :
  a <= b ->
  (forall x, a <= x <= b -> f x <= g x) ->
  (forall x, a <= x -> x.+1 <= b -> f x <= f x.+1 <= (g x).+1) ->
  f a <= n <= g b ->
  exists2 m, a <= m <= b & f m <= n <= g m.
Proof.
  move/leP.
  elim: b / => [| b /leP leq_ab IH] leq_fg touching ineq_n.
  - by exists a; rewrite ?leqnn.
  - case: (leqP n (g b)) => [le_n_gb | lt_gb_n].
    + case: IH.
      * by move=> ??; apply: leq_fg; lia.
      * by move=> ???; apply: touching; lia.
      * by lia.
      * move=> m ineq_m ineq_fgm.
        exists m => //.
        by lia.
    + have ? := touching b leq_ab (leqnn _).
      by exists b.+1; lia.
Qed.

Lemma total_bound_chain_forms_closed_interval m s lb ub :
  [&& lower_bound_bottomup s <= lb, lb <= ub & ub <= upper_bound_bottomup s] ->
  lower_bound_total s lb <= m <= upper_bound_total s ub ->
  exists2 n, lb <= n <= ub & lower_bound_total s n <= m <= upper_bound_total s n.
Proof.
  move=> ineq_bound ineq_m.
  case: (@interval_chain_forms_closed_interval (lower_bound_total s) (upper_bound_total s) lb ub m) => //.
  - by lia.
  - by move=> ??; apply: leq_total_bound; lia.
  - by move=> ???; apply: consecutive_total_bounds_touch_each_other; lia.
  - by move=> n ??; exists n.
Qed.

(******************************************************************************)
(* Step 4: Prove the existence of a forest in which the number of nodes is    *)
(*         included in the bound defined in Step 3                            *)
(******************************************************************************)

Proposition in_total_boundP (n m : nat) (s : leave_spec) :
  lower_bound_bottomup s <= n <= upper_bound_bottomup s ->
  reflect (exists f, [/\ count_node_forest f = m, size f = n & satisfy_leave_spec f s]) (lower_bound_total s n <= m <= upper_bound_total s n).
Proof.
  rewrite /lower_bound_total /upper_bound_total.
  move=> ineq_n.
  apply: (iffP idP).
  - elim: s => [| l0 s' IH] /= in m n ineq_n *.
    + move: ineq_n; rewrite !leqn0; do 2!move/eqP->.
      by exists [::].
    + move=> ineq_m.
      set lb := maxn _ _ in ineq_m.
      set ub := minn _ _ in ineq_m.
      (* By the combination of total_bound_chain_forms_closed_interval and the      *)
      (* induction hypothesis, for all m' \in [lb, ub], we obtain a forest of size  *)
      (* m' satisfying the spec s'. See total_bound_chain_forms_closed_interval.    *)
      case: (@total_bound_chain_forms_closed_interval (m - n) s' lb ub).
      * by move: (leq_bottomup_bound s'); lia.
      * by rewrite /lower_bound_total /upper_bound_total; lia.
      * move=> n' ineq_n' ineq_m'.
        case: (IH (m - n) n').
        -- by lia.
        -- by rewrite /lower_bound_total /upper_bound_total in ineq_m'; lia.
        -- move=> f' [Ecount Esize sat].
           exists (pairing_lift (n' - (n - l0)) f' ++ nseq l0 L); split.
           ++ by rewrite count_node_forest_cat count_node_forest_pairing_lift ?Ecount ?Esize ?count_node_forest_nseq /=; lia.
           ++ by rewrite size_cat size_pairing_lift Esize ?size_nseq; lia.
           ++ apply/andP; split.
              ** by rewrite count_cat count_mem_L_pairing_lift count_nseq mul1n.
              ** rewrite subforest_cat subforest_pairing_lift.
                 by rewrite subforest_nseq flatten_nseq_nil cats0.
  - elim: s => [| l0 s' IH] /= in m n ineq_n *.
    + case => f [Ecount _ /eqP Ef].
      rewrite Ef in Ecount.
      by rewrite -Ecount.
    + case => f [Ecount Esize /andP [/eqP EcountL sat]].
      set f' := subforest f.
      have ineq_size_f' : lower_bound_bottomup s' <= size f' <= upper_bound_bottomup s'.
      { by apply/in_bottomup_boundP; exists f' => //. }
      have ex_f' : exists f, [/\ count_node_forest f = m - n, size f = size f' & satisfy_leave_spec f s'].
      { 
        exists f'; split => //.
        (* Note: To obtain the equality (n + m) - n = m, use addKn. It is hard to search. *)
        by rewrite -Ecount (eq_count_node_forest f) Esize addKn.
      }
      have {ex_f'} := IH _ _ ineq_size_f' ex_f'.
      set lb := maxn _ _.
      set ub := minn _ _. 
      have ineq_n' := in_size_forest f.
      rewrite EcountL Esize -/f' in ineq_n'.
      have : lower_bound_total s' lb <= lower_bound_total s' (size f').
      { by apply: homo_lower_bound_total; lia. }
      have : upper_bound_total s' (size f') <= upper_bound_total s' ub.
      { by apply: homo_upper_bound_total; lia. }
      have : n <= m.
      { by rewrite -Esize -Ecount eq_count_node_forest leq_addr. }
      rewrite /lower_bound_total /upper_bound_total.
      by lia.
Qed.

(******************************************************************************)
(* Step 5: Speed up the functions defined in Step 3                           *)
(******************************************************************************)

Definition lower_bounds_topdown (s : leave_spec) (n : nat) :=
  belast n (scanl subn n s).

Definition upper_bounds_topdown (s : leave_spec) (n : nat) :=
  belast n (scanl (fun ub l0 => (ub - l0).*2) n s).

Definition lower_bounds_bottomup s :=
  scanr (fun l0 lb : nat => l0 + uphalf lb) 0 s.

Definition upper_bounds_bottomup s :=
  scanr (fun l0 ub : nat => l0 + ub) 0 s.

Definition lower_bounds_backforth' s n :=
  map2 maxn (lower_bounds_bottomup s) (lower_bounds_topdown s n).

Definition upper_bounds_backforth' s n :=
  map2 minn (upper_bounds_bottomup s) (upper_bounds_topdown s n).

Lemma lower_bounds_backforth'E l0 s n :
  lower_bounds_backforth' (l0 :: s) n =
    maxn (lower_bound_bottomup (l0 :: s)) n :: lower_bounds_backforth' s (n - l0).
Proof. by rewrite /lower_bounds_backforth' /lower_bounds_bottomup scanrE. Qed.

Lemma upper_bounds_backforth'E l0 s n :
  upper_bounds_backforth' (l0 :: s) n =
    minn (upper_bound_bottomup (l0 :: s)) n :: upper_bounds_backforth' s (n - l0).*2.
Proof. by rewrite /upper_bounds_backforth' /upper_bounds_bottomup scanrE. Qed.

Definition lower_bound_total' s n :=
  sumn (lower_bounds_backforth' s n).

Definition upper_bound_total' s n :=
  sumn (upper_bounds_backforth' s n).

Lemma lower_bound_lower_bounds_backforth' s n :
  n <= lower_bound_bottomup s ->
  lower_bounds_backforth' s n = lower_bounds_backforth' s (lower_bound_bottomup s).
Proof.
  elim: s => //= l0 s' IH in n *.
  move=> leq_n.
  rewrite !lower_bounds_backforth'E /=.
  congr (_ :: _).
  - by rewrite maxnn; apply/maxn_idPl.
  - rewrite addKn !IH //.
    + by apply: leq_uphalf.
    + by lia.
Qed.

Lemma upper_bound_upper_bounds_backforth' s n :
  upper_bound_bottomup s <= n ->
  upper_bounds_backforth' s n = upper_bounds_backforth' s (upper_bound_bottomup s).
Proof.
  elim: s => //= l0 s' IH in n *.
  move=> leq_n.
  rewrite !upper_bounds_backforth'E /=.
  congr (_ :: _).
  - by rewrite minnn; apply/minn_idPl.
  - rewrite addKn !IH //.
    + by rewrite -mul2n leq_pmull.
    + by lia.
Qed.

Lemma lower_bounds_backforth_equiv s n :
  lower_bound_bottomup s <= n ->
  lower_bounds_backforth' s n = lower_bounds_backforth s n.
Proof.
  elim: s => //= l0 s' IH in n *.
  move=> geq_n.
  rewrite lower_bounds_backforth'E /=.
  congr (_ :: _).
  - by apply/maxn_idPr.
  - set lbb' := lower_bound_bottomup s'.
    case: (ltnP lbb' (n - l0)).
    + by move=> ?; apply/IH/ltnW.
    + by move=> le_nl0_lbb'; rewrite lower_bound_lower_bounds_backforth' // IH.
Qed.

Lemma upper_bounds_backforth_equiv s n :
  n <= upper_bound_bottomup s ->
  upper_bounds_backforth' s n = upper_bounds_backforth s n.
Proof.
  rewrite /upper_bound_total /upper_bound_total'.
  elim: s => //= l0 s' IH in n *.
  move=> leq_n.
  rewrite upper_bounds_backforth'E /=.
  congr (_ :: _).
  - by apply/minn_idPr.
  - set ubb' := upper_bound_bottomup s'.
    case: (ltnP (n - l0).*2 ubb').
    + by move=> ?; apply/IH/ltnW.
    + by move=> le_ubb'_nl02; rewrite upper_bound_upper_bounds_backforth' // IH.
Qed.

Lemma lower_bound_total_equiv s n :
  lower_bound_bottomup s <= n ->
  lower_bound_total' s n = lower_bound_total s n.
Proof. by move=> ?; rewrite /lower_bound_total' lower_bounds_backforth_equiv. Qed.

Lemma upper_bound_total_equiv s n :
  n <= upper_bound_bottomup s ->
  upper_bound_total' s n = upper_bound_total s n.
Proof. by move=> ?; rewrite /upper_bound_total' upper_bounds_backforth_equiv. Qed.

Require Extraction.
Extract Inductive list => "list" [ "[]" "( :: )" ].
Extract Inductive nat => "int" [ "0" "succ" ] "(fun fO fS n -> if n = 0 then fO () else fS (n - 1))".
Extract Inlined Constant addn => "( + )".
Extract Inlined Constant subn => "( - )".
Extract Inlined Constant maxn => "max".
Extract Inlined Constant minn => "min".
Extract Inlined Constant double => "(fun n -> n * 2)".
Extract Inlined Constant half => "(fun n -> n / 2)".
Extract Inlined Constant uphalf => "(fun n -> (n + 1) / 2)".
Extraction Inline scanr_aux.

Extraction "folia" lower_bound_bottomup upper_bound_total'.
