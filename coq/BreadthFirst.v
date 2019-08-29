(** Authors:
Simon Boulier (INRIA) for the part before the def. of γ (without the simple lemmas)
Ralph Matthes (IRIT - CNRS and Univ. of Toulouse) for the three different methods of verification, all suggested in 1995 and for the forest-based verification and new system view found in 2018

occasional references are made to the paper "Martin Hofmann’s case for non-strictly positive
data types" by U. Berger, R. Matthes and A. Setzer, to appear in LIPIcs vol. 130 (TYPES 2018 post-proceedings)

*)

From TypingFlags Require Import Loader.


Inductive tree :=
| leaf : nat -> tree
| node : tree -> nat -> tree -> tree.

Definition ex1 : tree.
Proof.
  refine (node _ 1 (leaf 3)).
  refine (node _ 2 _).
  - exact (node (leaf 6) 4 (leaf 7)).
  - refine (node _ 5 (leaf 9)).
    exact (node (leaf 10) 8 (leaf 11)).
Defined.

Require Import List.
Import ListNotations.

Fixpoint zip (l1 l2 : list (list nat)) : list (list nat) :=
  match l1, l2 with
  | [], l => l
  | l, [] => l
  | x :: l, x' :: l' => (x ++ x') :: (zip l l')
  end.

Lemma zip_with_nil (l: list (list nat)): zip l [] = l.
Proof.
  destruct l; reflexivity.
Qed.

Lemma zip_assoc (l1 l2 l3: list (list nat)):
  zip l1 (zip l2 l3) = zip (zip l1 l2) l3.
Proof.
  revert l2 l3.
  induction l1.
  - reflexivity.
  - destruct l2.
    + reflexivity.
    + destruct l3.
      * reflexivity.
      * simpl.
        rewrite app_assoc.
        f_equal.
        apply IHl1.
Qed.

Fixpoint niv (t : tree) : list (list nat) :=
  match t with
  | leaf n => [[n]]
  | node tl n tr => [n] :: zip (niv tl) (niv tr)
  end.

Definition flatten: list (list nat) -> list nat := @concat nat.

Definition breadthfirst_spec t := flatten (niv t).

Compute (niv ex1).
Compute (breadthfirst_spec ex1).

Unset Guard Checking.
Inductive Rou :=
| Over : Rou
| Next : ((Rou -> list nat) -> list nat) -> Rou.
Set Guard Checking.

Definition unfoldRou (c : Rou) (k : Rou -> list nat) : list nat :=
  match c with
  | Over => k Over
  | Next f => f k
  end.

Fixpoint br (t : tree) (c : Rou) : Rou :=
  match t with
  | leaf n => Next (fun k => n :: unfoldRou c k)
  | node tl n tr => Next (fun k => n :: unfoldRou c (fun c1 => k (br tl (br tr c1))))
  end.

Unset Guard Checking.
Fixpoint extract (c : Rou) : list nat :=
  match c with
  | Over => []
  | Next f => f extract
  end.
Set Guard Checking.

Definition breadthfirst t := extract (br t Over).

Compute (br (leaf 3) Over).
Compute (br (leaf 2) (br (leaf 3) Over)).
Compute (breadthfirst ex1).
Print Assumptions breadthfirst.

(** ** Verification of the algorithm in Martin Hofmann's own style *)
(** Section in paper entitled "Martin Hofmann's verification of partial correctness" *)

Fixpoint γ (ll:list (list nat))(c: Rou): Rou :=
  match ll with
  | [] => c
  | l :: ll1 => Next (fun k => l ++ unfoldRou c (fun c1 => k (γ ll1 c1)))
  end.

Lemma MH_LemmaA (ll:list (list nat)): extract(γ ll Over) = flatten ll.
Proof.
  induction ll.
  - reflexivity.
  - simpl.
    f_equal.
    exact IHll.
Qed.

(** the following is required to get the proofs with Coq through although
    a pencil-and-paper proof is possible that all these equations hold
    w.r.t. convertibility for all input lists *)
Require Import Logic.FunctionalExtensionality.

Lemma MH_LemmaB (ll ll':list (list nat))(c: Rou): γ ll (γ ll' c) = γ (zip ll ll') c.
Proof.
  revert ll' c.
  induction ll.
  - simpl. reflexivity.
  - induction ll'.
    + simpl. reflexivity.
    + simpl.
      intro c.
      f_equal.
      apply functional_extensionality; intro k.
      rewrite app_assoc.
      f_equal.
      f_equal.
      clear c IHll'.
      apply functional_extensionality; intro c.
      f_equal.
      apply IHll.
Qed.

Lemma MH_LemmaC (t: tree)(c: Rou): br t c = γ (niv t) c.
Proof.
  revert c.
  induction t as [n | tl IHt1 n tr IHt2].
  - simpl. reflexivity. (* thanks to eta-equality *)
  - simpl.
    assert( aux : forall (c: Rou), br tl (br tr c) = γ (zip (niv tl) (niv tr)) c).
    { intro c.
      rewrite IHt2.
      rewrite IHt1.
      apply MH_LemmaB.
    }
    intro c.
    f_equal.
    apply functional_extensionality; intro k.
    f_equal.
    f_equal.
    clear c.
    apply functional_extensionality; intro c.
    f_equal.
    apply aux.
Qed.

Theorem MH_Verif (t: tree): breadthfirst t = breadthfirst_spec t.
Proof.
  unfold breadthfirst, breadthfirst_spec.
  rewrite MH_LemmaC.
  apply MH_LemmaA.
Qed.

Print Assumptions MH_Verif.


(** ** Verification of the algorithm via a non-strictly positive relation *)
(** It does not need functional extensionality even in the Coq proof. *)
(** Section in paper entitled "Verification by a non-strictly positive inductive relation" *)

Definition isextractor (R: Rou -> list(list nat) -> Prop)(ll: list(list nat))(k:Rou -> list nat): Prop :=
    forall (c: Rou)(ll1: list(list nat)), R c ll1 -> k c = flatten(zip ll ll1).

Unset Guard Checking.
Inductive rep: Rou -> list (list nat) -> Prop :=
| overrep: rep Over []
| nextrep: forall (f: (Rou -> list nat) -> list nat)(l: list nat)(ll: list(list nat)), (forall (k: Rou -> list nat)(ll': list(list nat)), isextractor rep ll' k -> f k = l ++ flatten(zip ll' ll)) -> rep (Next f) (l::ll).
(** is a non-strictly positive inductive proposition - could equivalently be defined impredicatively thanks to impredicativity of Prop *)

Fixpoint rep_ind (R : Rou -> list (list nat) -> Prop)(HypO: R Over [])
         (HypN: forall (f: (Rou -> list nat) -> list nat)(l: list nat)(ll: list(list nat)), (forall (k: Rou -> list nat)(ll': list(list nat)), isextractor R ll' k -> f k = l ++ flatten(zip ll' ll)) -> R (Next f) (l::ll)) (c : Rou) (l : list (list nat))(Hyp: rep c l) {struct Hyp}: R c l :=
  match Hyp in (rep c0 l0) return (R c0 l0) with
  | overrep => HypO
  | nextrep f0 l0 ll0 Hyp0 =>
    HypN _ _ _ (fun k ll' HypR => Hyp0 _ _ (fun c0 ll1 Hyp1 => HypR _ _ (rep_ind R HypO HypN c0 ll1 Hyp1)))
  end.
(* interactively:
Proof.
  refine (match Hyp in (rep c0 l0) return (R c0 l0) with
| overrep => HypO
| nextrep f0 l0 ll0 Hyp0 => _
          end).
apply HypN.
intros k ll' HypR.
apply Hyp0.
intros c0 ll1 Hyp1.
apply HypR.
apply (rep_ind R HypO HypN c0 ll1 Hyp1).
Defined.
*)
Set Guard Checking.


Lemma rep_Lemma1: isextractor rep [] extract.
Proof.
  red.
  intros ? ? Hyp.
  induction Hyp.
  - reflexivity.
  - simpl.
    change ll with (zip [] ll).
    apply H.
    intros ? ? Hyp.
    exact Hyp.
Qed.


Lemma rep_Lemma2_close_to_paper: forall (t: tree)(c: Rou)(ll: list(list nat)),
    rep c ll -> rep (br t c) (zip (niv t) ll).
Proof.
  induction t as [n | tl IHt1 n tr IHt2].
  - intros ? ?. intro Hyp; destruct ll.
    + simpl.
      inversion Hyp; subst.
      apply nextrep.
      intros ? ? Hyp1.
      fold (isextractor rep ll' k) in Hyp1.
      simpl.
      f_equal.
      apply Hyp1.
      apply overrep.
    + simpl.
      inversion Hyp; subst.
      change ( forall (k : Rou -> list nat) (ll' : list (list nat)),
       isextractor rep ll' k ->
       f k = l ++ flatten (zip ll' ll)) in H1.
      apply nextrep.
      intros ? ? Hyp1.
      fold (isextractor rep ll' k) in Hyp1.
      simpl.
      f_equal.
      apply H1.
      assumption.
  - intros ? ?; intro Hyp; destruct ll.
    + simpl.
      inversion Hyp; subst.
      apply nextrep.
      intros ? ? Hyp1.
      fold (isextractor rep ll' k) in Hyp1.
      simpl.
      f_equal.
      apply Hyp1.
      apply IHt1.
      replace (niv tr) with (zip (niv tr) []) by (apply zip_with_nil).
      apply IHt2.
      apply overrep.
    + simpl.
      inversion Hyp; subst.
      change ( forall (k : Rou -> list nat) (ll' : list (list nat)),
       isextractor rep ll' k ->
       f k = l ++ flatten (zip ll' ll)) in H1.
      apply nextrep.
      intros ? ? Hyp1.
      fold (isextractor rep ll' k) in Hyp1.
      simpl.
      f_equal.
      rewrite zip_assoc.
      apply H1.
      red; intros ? ? Hyp2.
      rewrite <- zip_assoc.
      apply Hyp1.
      rewrite <- zip_assoc.
      apply IHt1.
      apply IHt2.
      assumption.
Qed.

(** here is a variant of the proof that had been obtained before - with inversion on [Rou]
    but some detour later *)
Lemma rep_Lemma2: forall (t: tree)(c: Rou)(ll: list(list nat)),
    rep c ll -> rep (br t c) (zip (niv t) ll).
Proof.
  induction t as [n | tl IHt1 n tr IHt2].
  - intros ? ?. intro Hyp; destruct Hyp.
    (** the proof in the paper is more elementary, by case analysis on [ll], see before *)
    + simpl.
      apply nextrep.
      intros ? ? Hyp1.
      simpl.
      f_equal.
      apply Hyp1.
      apply overrep.
    + simpl.
      apply nextrep.
      intros ? ? Hyp1.
      simpl.
      f_equal.
      apply H.
      intros ? ? .
      apply Hyp1.
  - intros ? ?; intro Hyp; destruct Hyp.
    + simpl.
      apply nextrep.
      intros ? ? Hyp1.
      simpl.
      f_equal.
      apply Hyp1.
      apply IHt1.
      replace (niv tr) with (zip (niv tr) []) by (apply zip_with_nil).
      apply IHt2.
      apply overrep.
    + simpl.
      apply nextrep.
      intros ? ? Hyp1.
      simpl.
      f_equal.
      set (k0 := fun c1 : Rou => k (br tl (br tr c1))).
      assert (aux: isextractor rep (zip ll'(zip (niv tl) (niv tr))) k0).
      { red.
        intros ? ? Hyp2.
        unfold k0.
        set (aux2 := Hyp1 _ _ (IHt1 _ _ (IHt2 _ _ Hyp2))).
        rewrite aux2.
        f_equal.
        do 3 rewrite zip_assoc.
        reflexivity.
      }
      do 2 rewrite zip_assoc.
      apply H.
      intros ? ? Hyp2.
      red in aux.
      rewrite (aux _ _ Hyp2).
      f_equal.
      rewrite zip_assoc.
      reflexivity.
Qed.

Theorem rep_Verif (t: tree): breadthfirst t = breadthfirst_spec t.
Proof.
  unfold breadthfirst, breadthfirst_spec.
  apply rep_Lemma1; fold niv.
  replace (niv t) with (zip (niv t) []) by (apply zip_with_nil).
  apply rep_Lemma2.
  exact overrep.
Qed.

Print Assumptions rep_Verif.

(** ** Verification through the extension to forests *)
(** Section in paper entitled "A proof of the correctness of [breadthfirst] using forests" *)

Fixpoint depth (t: tree): nat :=
  match t with
  | leaf _ => 1
  | node tl _ tr => 1 + max (depth tl) (depth tr)
  end.

Definition forest: Set := list tree.

Fixpoint depthf (ts: forest): nat :=
  match ts with
  | [] => 0
  | t::ts' => max (depth t) (depthf ts')
  end.

Fixpoint nivf (ts: forest): list(list nat) :=
  match ts with
  | [] => []
  | t::ts' => zip (niv t) (nivf ts')
  end.

Fixpoint roots (ts: forest): list nat :=
  match ts with
  | [] => []
  | leaf n :: ts' => n::roots ts'
  | node _ n _ :: ts' => n::roots ts'
  end.

Fixpoint sub (ts: forest): forest :=
  match ts with
  | [] => []
  | leaf _ :: ts' => sub ts'
  | node tl _ tr :: ts' => tl::tr::sub ts'
  end.

Definition breadthfirstf_spec (ts: forest) : list nat := flatten (nivf ts).

Require Import FunInd.
Functional Scheme zip_ind := Induction for zip Sort Prop.
Functional Scheme sub_ind := Induction for sub Sort Prop.

(** the following three lemmas are not needed later *)

(** auxiliary *)
Lemma lengthzip (ll1 ll2: list (list nat)): length (zip ll1 ll2) = max (length ll1) (length ll2).
Proof.
  functional induction (zip ll1 ll2) using zip_ind.
  - reflexivity.
  - reflexivity.
  - simpl. f_equal. assumption.
Qed.

Lemma lengthniv (t: tree): length (niv t) = depth t.
Proof.
  induction t as [n | tl IHt1 n tr IHt2].
  - reflexivity.
  - simpl.
    f_equal.
    rewrite <- IHt1, <- IHt2.
    apply lengthzip.
Qed.    

Lemma lengthnivf (ts: forest): length (nivf ts) = depthf ts.
Proof.
  induction ts as [ | t ts IHts].
  - reflexivity.
  - simpl.
    rewrite <- IHts.
    rewrite <- lengthniv.
    apply lengthzip.
Qed.

Require Import Arith.Le.
Require Import Arith.PeanoNat.
Require Import Arith.Compare_dec.
Require Import Arith.Max. (* a deprecated file *)

(** five preparatory lemmas *)

Lemma depthgeone (t: tree): 1 <= depth t.
Proof.
  destruct t as [n | tl n tr].
  - simpl. apply le_refl.
  - simpl. apply le_n_S. apply le_0_n.
Qed.

(** should be in the library *)
Lemma maxge1 (n1 n2 m: nat): n1 >= m -> max n1 n2 >= m.
Proof.
  generalize (le_ge_dec n1 n2).
  intros [Hyp | Hyp] H.
  - rewrite max_r.
    + apply le_trans with n1; assumption.
    + assumption.
  - rewrite max_l; assumption.
Qed.
      
Lemma depthfgeone (ts: forest): ts <> [] -> 1 <= depthf ts.
Proof.
  destruct ts as [ | t ts].
  - intro Hyp. destruct Hyp. reflexivity.
  - intro Hyp; clear Hyp.
    simpl. apply maxge1.
    apply depthgeone.
Qed.

Lemma depthfleaf (n: nat)(ts: forest): ts <> [] -> depthf (leaf n :: ts) = depthf ts.
Proof.
  destruct ts as [ | t ts].
  - intro Hyp. destruct Hyp. reflexivity.
  - intro Hyp; clear Hyp.
    change (depthf (leaf n :: t :: ts)) with (max (depth(leaf n)) (depthf(t::ts))).
    rewrite max_r.
    + reflexivity.
    + apply depthfgeone. intro Hyp. discriminate.
Qed.

Require Import Lia.  (** instead of Omega *)

Lemma depthnode (n: nat)(tl tr: tree): depth(node tl n tr) = max (depth tl) (depth tr) + 1.
Proof.
  simpl.
  lia.
Qed.

(** important lemma for justification of definition of [cforest] *)
Lemma depthsub (ts: forest): ts <> [] -> depthf(ts) = depthf(sub ts) + 1.
Proof.
  functional induction (sub ts) using sub_ind.
  - intro Hyp. destruct Hyp. reflexivity.
  - intro Hyp; clear Hyp.
    destruct ts' as [| t ts'].
    + reflexivity.
    + rewrite <- IHf.
      * apply depthfleaf.
        intro Hyp. discriminate.
      * intro Hyp. discriminate.
  - intro Hyp; clear Hyp.      
    destruct ts' as [| t ts'].
    + simpl.
      rewrite (max_l _ 0); lia.
    + change (depthf (node tl _x tr :: t :: ts')) with (max (depth (node tl _x tr)) (depthf (t :: ts'))).
      rewrite depthnode.
      rewrite IHf.
      2: { intro Hyp. discriminate. }
      change (depthf (tl :: tr :: sub (t :: ts'))) with (max (depth tl) (max (depth tr) (depthf (sub (t::ts'))))).
      rewrite plus_max_distr_r.
      f_equal.
      symmetry.
      apply max_assoc.
Qed.     

(** two auxiliary lemmas: *)
Lemma nivrootssuboneelement (t: tree): nivf [t] = roots [t] :: nivf (sub [t]).
Proof.
  destruct t as [n | tl n tr].
  - reflexivity.
  - simpl.
    rewrite zip_with_nil.
    reflexivity.
Qed.  

Lemma nivrootssubmoreelements (t: tree)(ts: forest): zip (niv t) (roots ts :: nivf (sub ts)) = roots (t :: ts) :: nivf (sub (t :: ts)).
Proof.
  destruct t as [n | tl n tr].
  - simpl. reflexivity.
  - simpl. f_equal. symmetry. apply zip_assoc.
Qed.

(* important lemma for the verification of the extraction process out of [cforest] *)
Lemma nivfrootssub (ts: forest): ts <> [] -> nivf ts = roots ts :: nivf (sub ts).
Proof.
  induction ts as [ | t ts IHts].
  - intro Hyp. destruct Hyp. reflexivity.
  - intro Hyp; clear Hyp.
    destruct ts as [| t' ts].
    + apply nivrootssuboneelement.
    + change (nivf (t :: t' :: ts)) with (zip(niv t)(nivf (t'::ts))).
      rewrite IHts.
      2: { intro Hyp. discriminate. }
      clear IHts.
      apply nivrootssubmoreelements.
Qed.

    
Definition next (g: list nat -> list nat) (c: Rou): Rou :=  Next(fun k: Rou -> list nat => g(k c)).
Definition addroots (ts: forest): list nat -> list nat := app (roots ts).

Require Import Lia.

(*
Require Import Program.
Program Fixpoint cforest' (ts: forest) {measure (depthf ts)}: Rou :=
  match ts with
  | [] => Over
  | t::ts' => next (addroots ts) (cforest' (sub ts))
  end.
Next Obligation.
  rewrite (depthsub (t::ts')).
  2: { intro Hyp. discriminate. }
  lia.
Qed.

(* the following lemma does not work!
Lemma cforest'_cons (t: tree)(ts: forest): cforest' (t::ts) = next (addroots (t::ts)) (cforest' (sub (t::ts))).
Proof.
  - reflexivity.
Qed.
*)

Program Fixpoint cforest'_ind (P: forest -> Prop)(Hyp1: P [])(Hyp2: forall ts, ts <> [] -> P (sub ts) -> P ts)(ts: forest) {measure (depthf ts)}: P ts :=
  match ts with
  | [] => Hyp1
  | t::ts' => Hyp2 ts _ (cforest'_ind P Hyp1 Hyp2 (sub ts))
  end.
Next Obligation.
    rewrite (depthsub (t::ts')).
  2: { intro Hyp. discriminate. }
  lia.
Qed.
*)

Require Import Recdef.
Function cforest (ts: forest) {measure depthf ts}: Rou :=
  match ts with
  | [] => Over
  | t::ts' => next (addroots (t::ts')) (cforest (sub (t::ts')))
  end.
Proof.
  intros ts t ts' _.
  rewrite (depthsub (t::ts')).
  2: { intro Hyp. discriminate. }
  lia.
Defined.

Check cforest_ind.
Check cforest_equation.

Lemma cforest_cons (t: tree)(ts: forest): cforest (t::ts) = next (addroots (t::ts)) (cforest (sub (t::ts))).
Proof.
  apply cforest_equation. 
Qed.

Lemma cforest_extract_Lemma (ts: forest): extract (cforest ts) = breadthfirstf_spec ts.
Proof.
  functional induction (cforest ts) using cforest_ind.
  - reflexivity.
  - assert (Neq: t::ts' <> []) by (intro Hyp; discriminate).
    generalize Neq IHr.
    generalize (t::ts').
    clear t ts' IHr Neq.
    intros ts Neq IH.
    simpl.
    rewrite IH.
    unfold breadthfirstf_spec, addroots.
    rewrite (nivfrootssub ts).
    2: assumption.
    reflexivity.
Qed.

Lemma br_cforest_Lemma (t: tree)(ts: forest): br t (cforest ts) = cforest (t::ts).
Proof.
  revert ts.
  induction t as [n | tl IHt1 n tr IHt2]; intro ts.
  - functional induction (cforest ts) using cforest_ind.
    + reflexivity.
    + assert (Neq: t::ts' <> []) by (intro Hyp; discriminate).
      generalize Neq IHr.
      generalize (t::ts').
      clear t ts' IHr Neq.
      intros ts Neq IH.
      simpl.
      rewrite cforest_cons.
      reflexivity.
  - functional induction (cforest ts) using cforest_ind.
    + simpl.
      change Over with (cforest []).
      rewrite IHt2.
      rewrite IHt1.
      rewrite (cforest_cons (node tl n tr)).
      reflexivity.
    + assert (Neq: t::ts' <> []) by (intro Hyp; discriminate).
      generalize Neq IHr.
      generalize (t::ts').
      clear t ts' IHr Neq.
      intros ts Neq _.
      simpl.
      rewrite IHt2.
      rewrite IHt1.
      rewrite (cforest_cons (node tl n tr)).
      reflexivity.
Qed.
    
(** ** Verification of the algorithm in the predicative style *)
(** in two parts *)

(** *** Section in paper entitled "A predicative version of [breadthfirst]" *)

Definition Rou' := list(list nat -> list nat).

Fixpoint Φ (gs: Rou'): Rou :=
  match gs with
  | [] => Over
  | g::gs' => next g (Φ gs')
  end.

(** "predicative" version of [br] *)
Fixpoint br' (t: tree)(gs: Rou'): Rou' :=
  match t, gs with
  | leaf n, [] => [cons n]
  | leaf n, g::gs' => (fun l:list nat => n::g l)::gs'
  | node tl n tr, [] => (cons n) :: br' tl (br' tr [])
  | node tl n tr, g::gs' => (fun l:list nat => n::g l) :: br' tl (br' tr gs')
  end.

Lemma br'_Lemma (t: tree)(gs: Rou'): Φ(br' t gs) = br t (Φ gs).
Proof.
  revert gs.
  induction t as [n | tl IHt1 n tr IHt2]; destruct gs as [| g gs'].
  - reflexivity.
  - reflexivity.
  - simpl; unfold next.
    f_equal.
    apply functional_extensionality; intro k.
    do 2 f_equal.
    change Over with (Φ []).
    rewrite <- (IHt2 []).
    apply IHt1.
  - simpl; unfold next.
    f_equal.
    apply functional_extensionality; intro k.
    do 3 f_equal.
    rewrite <- IHt2.
    apply IHt1.
Qed.

Fixpoint extract' (gs: Rou'): list nat :=
  match gs with
  | [] => []
  | g::gs' => g(extract' gs')
  end.

Lemma extract'_Lemma (gs: Rou'): extract' gs = extract (Φ gs).
Proof.
  induction gs as [| g gs' IH].
  - reflexivity.
  - simpl.
    f_equal.
    exact IH.
Qed.

Definition breadthfirst' (t: tree): list nat := extract'(br' t []).

Lemma breadthfirst'_ok (t: tree): breadthfirst' t = breadthfirst t.
Proof.
  unfold breadthfirst', breadthfirst.
  rewrite extract'_Lemma.
  rewrite br'_Lemma.
  reflexivity.
Qed.

(** standalone verification *)
Function traverse (ts: forest) {measure depthf ts}: Rou' :=
  match ts with
  | [] => []
  | t::ts' => addroots (t::ts') :: (traverse (sub (t::ts')))
  end.
Proof.
  intros ts t ts' _.
  rewrite (depthsub (t::ts')).
  2: { intro Hyp. discriminate. }
  lia.
Defined.

Check traverse_ind.
Check traverse_equation.

Lemma traverse_cons (t: tree)(ts: forest): traverse (t::ts) = addroots (t::ts) :: traverse (sub (t::ts)).
Proof.
  apply traverse_equation.
Qed.

Lemma extract'_traverse_Lemma (ts: forest): extract' (traverse ts) = breadthfirstf_spec ts.
Proof.
  functional induction (traverse ts) using traverse_ind.
  - reflexivity.
  - unfold extract'.
    transitivity (addroots ( t:: ts') (breadthfirstf_spec (sub (t :: ts')))).
    { f_equal. assumption. }
    clear IHr.
    do 2 rewrite <- cforest_extract_Lemma.
    rewrite cforest_cons.
    reflexivity.
Qed.

Lemma br'_traverse_Lemma (t: tree)(ts: forest): br' t (traverse ts) = traverse (t::ts).
Proof.
  revert ts.
  induction t; intro ts.
  - rewrite traverse_cons.
    functional induction (traverse ts) using traverse_ind; reflexivity.
  - rewrite traverse_cons.
    simpl sub.
    rewrite <- IHt1.
    rewrite <- IHt2.
    clear IHt1 IHt2.
    functional induction (traverse ts) using traverse_ind; reflexivity.
Qed.

Lemma breadthfirst'_verif (t: tree): breadthfirst' t = breadthfirst_spec t.
Proof.
  unfold breadthfirst', breadthfirst_spec.
  change ([]) with (traverse []).
  rewrite br'_traverse_Lemma.
  rewrite extract'_traverse_Lemma.
  unfold breadthfirstf_spec.
  simpl. rewrite zip_with_nil.
  reflexivity.
Qed.


(** *** Section in paper entitled "A simplified predicative version of [breadthfirst]" *)

Definition ψ (l: list nat): (list nat -> list nat) := fun l' => l ++ l'.

Definition Rou'' := list(list nat).
Definition Ψ: Rou'' -> Rou' := map ψ.

(** second refinement step for [br'] *)

Fixpoint br'' (t: tree)(ll: Rou''): Rou'' :=
  match t, ll with
  | leaf n, [] => [[n]]
  | leaf n, l::ll => (n::l)::ll
  | node tl n tr, [] => [n] :: br'' tl (br'' tr [])
  | node tl n tr, l::ll => (n::l) :: br'' tl (br'' tr ll)
  end.

Lemma br''_Lemma1 (t: tree)(ll: Rou''):  Ψ(br'' t ll) = br' t (Ψ ll).
Proof.
  revert ll.
  induction t as [n | tl IHt1 n tr IHt2]; destruct ll.
  - reflexivity.
  - reflexivity.
  - simpl.
    f_equal. (* thanks to eta-equality *)
    change (@nil (forall _ : list nat, list nat)) with (Ψ []).
    rewrite <- (IHt2 []).
    apply IHt1.
  - simpl.
    f_equal. (* thanks to eta-equality *)
    rewrite <- IHt2.
    apply IHt1.
Qed.


Lemma br''_Lemma2 (t: tree)(ll: Rou''): br'' t ll = zip (niv t) ll.
Proof.
  revert ll.
  induction t as [n | tl IHt1 n tr IHt2]; destruct ll.
  - reflexivity.
  - reflexivity.
  - simpl.
    f_equal.
    rewrite IHt2.
    rewrite zip_with_nil.
    apply IHt1.
  - simpl.
    f_equal.
    rewrite IHt2.
    rewrite <- zip_assoc.
    apply IHt1.
Qed.

Lemma Ψ_extract'_Lemma (ll: Rou''): flatten ll = extract' (Ψ ll).
Proof.
  induction ll.
  - reflexivity.
  - simpl.
    rewrite IHll.
    reflexivity.
Qed.

Definition breadthfirst'' (t: tree): list nat := flatten(br'' t []).

Lemma breadthfirst''_ok (t: tree): breadthfirst'' t = breadthfirst' t.
Proof.
  unfold breadthfirst'', breadthfirst'.
  rewrite Ψ_extract'_Lemma.
  f_equal.
  rewrite br''_Lemma1.
  reflexivity.
Qed.

Lemma breadthfirst''_verif (t: tree): breadthfirst'' t = breadthfirst_spec t.
Proof.
  unfold breadthfirst'', breadthfirst_spec.
  rewrite br''_Lemma2.
  rewrite zip_with_nil.
  reflexivity.
Qed.

(** ** the big picture *)
(** Section in paper entitled "Formal comparison of the obtained algorithms and proofs" *)

Record Sys: Type := mkSys {A: Set; Nil: A; g: tree->A->A; e: A->list nat}.
Definition correct (S: Sys): Prop := forall t, e S (g S t (Nil S)) = breadthfirst_spec t.
Definition simulation (S S': Sys)(R: A S -> A S' -> Prop): Prop := R (Nil S) (Nil S') /\ (forall a a', R a a' -> (forall t, R (g S t a) (g S' t a')) /\ e S a = e S' a').
Definition similar(S S': Sys): Prop := exists R, simulation S S' R.

Lemma similar_sym (S S': Sys): similar S S' -> similar S' S.
Proof.
  intro Hyp.
  destruct Hyp as [R Hypsim].
  destruct Hypsim as [Hyp1 Hyp23].
  exists (fun a' a => R a a').
  red.
  split.
  - assumption.
  - intros a' a HypR.
    split.
    + refine (proj1 (Hyp23 _ _ HypR)).
    + symmetry. refine (proj2 (Hyp23 _ _ HypR)).
Qed.

Lemma similarprescorrect (S S': Sys): similar S S' -> correct S' -> correct S.
Proof.
  intros Hypsim Hypcor.
  destruct Hypsim as [R Hypsim].
  destruct Hypsim as [Hyp1 Hyp23].
  red in Hypcor.
  red.
  intro t.
  rewrite <- (Hypcor t).
  refine (proj2 (Hyp23 _ _ _)).
  refine (proj1 (Hyp23 _ _ _) _).
  assumption.
Qed.
  
Definition functionalsimulation (S S': Sys)(φ: A S' -> A S): Prop := Nil S = φ(Nil S') /\ forall a', (forall t, g S t (φ a') = φ (g S' t a') ) /\ e S (φ a') = e S' a'.

Lemma functionalisspecialcase (S S': Sys)(φ: A S' -> A S): functionalsimulation S S' φ -> simulation S S' (fun a a' => a = φ a').
Proof.
  intros [ Hyp1 Hyp23].
  split.
  - assumption.
  - intros a a' Eq.
    subst.
    destruct (Hyp23 a') as [Hyp2 Hyp3].
    split; assumption.
Qed.

Corollary functionalsimulationissimilar (S S': Sys)(φ: A S' -> A S): functionalsimulation S S' φ -> similar S S'.
Proof.
  intro Hyp.
  exists (fun a a' => a = φ a').
  apply functionalisspecialcase.
  assumption.
Qed.

Definition zipniv (t: tree)(ll: list(list nat)): list(list nat) := zip (niv t) ll. 

Definition S_spec: Sys := mkSys (list(list nat)) [] zipniv flatten.

Lemma S_spec_correct: correct S_spec.
Proof.
  red.
  intros.
  unfold e, g, Nil; simpl.
  unfold zipniv.
  rewrite zip_with_nil.
  reflexivity.
Qed.

Definition S_MH: Sys := mkSys Rou Over br extract.

Definition γ_Over (ll: list(list nat)): Rou := γ ll Over.

Lemma S_MH_simulates_S_spec: functionalsimulation S_MH S_spec γ_Over.
Proof.
  red.
  split.
  - unfold Nil; simpl. reflexivity.
  - intro ll.
    split.
    + intro t.
      unfold g; simpl.
      unfold γ_Over, zipniv.
      rewrite MH_LemmaC.
      apply MH_LemmaB.
    + unfold e; simpl.
      apply MH_LemmaA.
Qed.    
  
Lemma S_MH_correct: correct S_MH.
Proof.
  apply (similarprescorrect S_MH S_spec).
  - refine (functionalsimulationissimilar _ _ _ S_MH_simulates_S_spec).
  - apply S_spec_correct.
Qed.

Print Assumptions S_MH_correct.

Lemma S_MH_simulates_S_spec_with_rep: simulation S_MH S_spec rep.
Proof.
  red.
  split.
  - exact overrep.
  - intros c ll Hyp.
    split.
    + intro t.
      unfold g; simpl.
      apply rep_Lemma2_close_to_paper.
      assumption.
    + unfold e; simpl.
      apply rep_Lemma1.
      assumption.
Qed.

Lemma S_MH_correct_with_rep: correct S_MH.
Proof.
  apply (similarprescorrect S_MH S_spec).
  - exists rep.
    apply S_MH_simulates_S_spec_with_rep.
  - apply S_spec_correct.
Qed.

Print Assumptions S_MH_correct_with_rep.

(** a small diversion on the comparison of [rep] with the simulation based on [γ_Over] - not in the paper *)

Definition Rep_MH: Rou -> list(list nat) -> Prop := fun c ll => c = γ_Over ll.

(** [rep] is a freely generated relation but not the "smallest" simulation we could work with; at least [Rep_MH] is contained in it *)
Lemma Rep_MH_contained_in_rep (c: Rou)(ll: list(list nat)): Rep_MH c ll -> rep c ll.
Proof.
  revert c.
  induction ll as [| l ll]; intros c HypR.
  - red in HypR.
    subst.
    change (γ_Over []) with Over.
    apply overrep.
  - red in HypR.
    subst.
    unfold γ_Over.
    simpl.
    apply nextrep.
    intros k ll' Hypk.
    f_equal.
    change (γ ll Over) with (γ_Over ll).
    rewrite (Hypk _ ll); try reflexivity.
    apply IHll.
    reflexivity.
Qed.
    
(** the following is only the documentation of a failure *)
Lemma rep_contained_in_Rep_MH_FAIL (c: Rou)(ll: list(list nat)): rep c ll -> Rep_MH c ll.
Proof.
  intro Hypr.
  induction Hypr using rep_ind.
  - reflexivity.
  - red.
    unfold γ_Over.
    simpl.
    f_equal.
    apply functional_extensionality; intro k.
    (* we would be able to replace [f k] thanks to [H] if we knew a lot about [k]'s values,
       but we know nothing about [k] at all *)
Abort.

(** end of small diversion *)

Definition S_forest: Sys := mkSys forest [] (@cons tree) breadthfirstf_spec.

Lemma S_spec_simulates_S_forest: functionalsimulation S_spec S_forest nivf.
Proof.
  red.
  split.
  - unfold Nil; simpl. reflexivity.
  - intro ts.
    split.
    + intro t.
      unfold g; simpl.
      reflexivity.
    + unfold e; simpl.
      reflexivity.
Qed.

Lemma S_MH_simulates_S_forest: functionalsimulation S_MH S_forest cforest.
Proof.
  red.
  split.
  - unfold Nil; simpl. reflexivity.
  - intro gs.
    split.
    + intro t.
      unfold g; simpl.
      apply br_cforest_Lemma.
    + unfold e; simpl.
      apply cforest_extract_Lemma.
Qed.

Lemma S_MH_correct_through_forests: correct S_MH.
Proof.
  apply (similarprescorrect S_MH S_forest).
  { refine (functionalsimulationissimilar _ _ _ S_MH_simulates_S_forest). }
  apply (similarprescorrect S_forest S_spec).
  { apply similar_sym.
    refine (functionalsimulationissimilar _ _ _ S_spec_simulates_S_forest). }
  apply S_spec_correct.
Qed.

Print Assumptions S_MH_correct_through_forests.


Lemma γ_Over_decomposes (ll: list(list nat)): γ_Over ll = Φ (Ψ ll).
Proof.
  induction ll.  
  - reflexivity.
  - unfold γ_Over; simpl; unfold next.
    f_equal.
    apply functional_extensionality; intro k.
    unfold ψ.
    do 2 f_equal.
    apply IHll.
Qed.
    
Definition S_pred1: Sys := mkSys Rou' [] br' extract'.

Lemma S_MH_simulates_S_pred1: functionalsimulation S_MH S_pred1 Φ.
Proof.
  red.
  split.
  - unfold Nil; simpl. reflexivity.
  - intro gs.
    split.
    + intro t.
      unfold g; simpl.
      symmetry.
      apply br'_Lemma.
    + unfold e; simpl.
      symmetry.
      apply extract'_Lemma.
Qed.

(** the extra simulation *)
Lemma S_pred1_simulates_S_forest: functionalsimulation S_pred1 S_forest traverse.
Proof.
  red.
  split.
  - unfold Nil; simpl. reflexivity.
  - intro ts.
    split.
    + intro t.
      unfold g; simpl.
      apply br'_traverse_Lemma.
    + unfold e; simpl.
      apply extract'_traverse_Lemma.
Qed.

(** the extra decompositions *)
Lemma traverse_decomposes (ts: forest): traverse ts = Ψ (nivf ts).
Proof.
  functional induction (traverse ts) using traverse_ind.
  - reflexivity.
  - rewrite IHr.
    rewrite (nivfrootssub (t::ts')).
    2: { intro Hyp. discriminate. }
    reflexivity.
Qed.

Lemma cforest_decomposes (ts: forest): cforest ts = Φ (traverse ts).
Proof.
  functional induction (cforest ts) using cforest_ind.
  - reflexivity.
  - rewrite IHr.
    rewrite traverse_cons.
    reflexivity.
Qed.

(** end of extra simulation / decompositions *)

Definition S_pred2: Sys := mkSys Rou'' [] br'' flatten.

Lemma S_pred1_simulates_S_pred2: functionalsimulation S_pred1 S_pred2 Ψ.
Proof.
  red.
  split.
  - unfold Nil; simpl. reflexivity.
  - intro ll.
    split.
    + intro t.
      unfold g; simpl.
      symmetry.
      apply br''_Lemma1.
    + unfold e; simpl.
      symmetry.
      apply Ψ_extract'_Lemma.
Qed.

(** we only prove functional simulation by the identity, but the systems are extensionally equal *)
Lemma S_pred2_simulates_S_spec: functionalsimulation S_pred2 S_spec (fun x => x).
Proof.
  red.
  split.
  - unfold Nil; simpl. reflexivity.
  - intro ll.
    split.
    + intro t.
      unfold g; simpl.
      apply br''_Lemma2.
    + unfold e; simpl.
      reflexivity.
Qed.

Lemma S_MH_correct_with_2_reductions: correct S_MH.
Proof.
  apply (similarprescorrect S_MH S_pred1).
  { refine (functionalsimulationissimilar _ _ _ S_MH_simulates_S_pred1). }
  apply (similarprescorrect S_pred1 S_pred2).
  { refine (functionalsimulationissimilar _ _ _ S_pred1_simulates_S_pred2). }
  apply (similarprescorrect S_pred2 S_spec).
  { refine (functionalsimulationissimilar _ _ _ S_pred2_simulates_S_spec). }
  apply S_spec_correct.
Qed.

Print Assumptions S_MH_correct_with_2_reductions.

