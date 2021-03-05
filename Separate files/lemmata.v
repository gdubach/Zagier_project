(*  File 1/3 of the proofs of Fermat's Two Squares Theorem                    *)
(*                          by G. Dubach and F. Muehlboeck, IST Austria, 2021 *)
(*                                                                            *)
(* This files contains ad-hoc tactics and a preliminary result on involutions.*)
(*                                                                            *)

From mathcomp Require Import all_ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import choice path finset finfun fintype bigop finmap.
From mathcomp Require Import ssralg order.
Require Import Psatz.
Import Order.TTheory GRing.Theory.
Set Implicit Argument.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope fset_scope.
Open Scope nat_scope.

(*  Ad-hoc tactics                                                            *)

Ltac mctocoq := intros; repeat match goal with
| [|- ?X * ?Y <= ?Z * ?W] => apply leq_mul; ((apply ltnW; assumption) || mctocoq; try reflexivity; nia)
| [H : context [addn] |- _] => unfold addn in H; unfold addn_rec in H; simpl in H
| [H : context [subn] |- _] => unfold subn in H; unfold subn_rec in H; simpl in H
| [H : context [muln] |- _] => unfold muln in H; unfold muln_rec in H; simpl in H
| [H : context [expn] |- _] => unfold expn in H; unfold expn_rec in H; simpl in H
| [H : context [leq _ _] |- _] => apply (elimT ssrnat.leP) in H; simpl in H
| [H : context [leq (S _) _] |- _] => apply (elimT ssrnat.ltP) in H; simpl in H
| [H : (leq _ _) = true |- _] => apply (Bool.reflect_iff _ _ ssrnat.leP) in H; simpl
| [H : (leq _ _) = false |- _] => apply (elimF ssrnat.leP) in H; simpl
| [H : context [_ == _] |- _] => apply (elimT eqnP) in H; simpl
| [H : context[Order.le] |- _] => rewrite Order.NatOrder.leEnat in H
| [ |- context[Order.le]] => rewrite Order.NatOrder.leEnat
| [ |- context [addn]] => unfold addn; unfold addn_rec; simpl
| [ |- context [subn]] => unfold subn; unfold subn_rec; simpl
| [ |- context [muln]] => unfold muln; unfold muln_rec; simpl
| [ |- context [expn]] => unfold expn; unfold expn_rec; simpl
| [ |- context [(leq _ _)]] => apply (introT ssrnat.leP); simpl
| [ |- context [_ == _]] => apply (introT eqnP); simpl
end.

Ltac mcnia := mctocoq; nia.
Ltac mclia := mctocoq; lia.

(* Two examples of uses of mcnia on remarkable identities for nat type        *)

Theorem third_remarkable_identity (a b:nat): (a>b) -> (a-b)*(a+b)=a^2-b^2.
Proof. mcnia. Qed.

Theorem sophie_germain_identity (a b:nat): 
(a^2+2*b^2-2*a*b>0) -> (a^2+2*b^2+2*a*b)*(a^2+2*b^2-2*a*b)=a^4+4*b^4.
Proof. mcnia. Qed.

Lemma pair_eq {S T : Type} (s s' : S) (t t' : T) : s = s' -> t = t' -> (s,t) = (s',t').
Proof.  intros Heqs Heqt; subst; reflexivity. Qed.

Ltac zag_solve := repeat match goal with
| [|- context [let (X,Y) := ?Z in _]] => destruct Z as [X Y]
| [|- context [if ?X then _ else _]] => case_eq X
| [|- _ -> _] => intros
| [|- (_, _) = (_,_)] => apply pair_eq
| [H : (_, _) = (_,_) |- _] => inversion H; clear H
end; try mcnia.

Ltac mcsimpl := repeat match goal with
| [H : context [_ == _] |- _] => apply (elimT eqnP) in H || apply (elimT eqP) in H
end.

Ltac hyp_progress H := match (type of H) with
| ?X -> ?Y => let Hold := fresh H "old" in rename H into Hold; assert (H : Y); [apply Hold; auto| clear Hold]
end.

Ltac destruct_boolhyp H := repeat (rewrite -Bool.orb_andb_distrib_r in H || rewrite -Bool.orb_andb_distrib_l in H); try (apply (elimT eqP) in H); (apply (elimT andP) in H; 
let H' := fresh H in destruct H as [H H']; try destruct_boolhyp H; try destruct_boolhyp H'; generalize dependent H')
|| (apply (elimT orP) in H; destruct H as [H | H]; try destruct_boolhyp H).
Ltac reflect_booleq H := apply (elimT eqP) in H.

Ltac is_assertion H X := match (type of H) with
| is_true (X) => rewrite /is_true
| X = true => idtac
| ~~ X = false => apply (introT negPf) in H; apply (elimT negPn) in H; is_assertion H X
| true = X => symmetry in H
| false = ~~ X => symmetry in H; is_assertion H X
end.

Ltac is_negation H X := match (type of H) with
| is_true (~~ X) => apply (elimT negPf) in H
| X = false => idtac
| ~~ X = true => apply (elimT negPf) in H
| false = X => symmetry in H
| true = ~~ X => symmetry in H; apply (elimT negPf) in H
end.

Lemma ltn_asymmetric : forall n m, (n < m) && (m < n) = false.
Proof.
  move => n m.
  destruct (n < m) eqn: hnm; destruct (m < n) eqn: hmn; try by auto.
  rewrite ltnNge leq_eqVlt negb_or in hnm. destruct_boolhyp hnm. move => hnm'.
  by rewrite hmn in hnm'.
Qed.

Ltac mccontradiction := by match goal with
| [H : context [?X], H' : context [?X] |- _] => is_assertion H X; is_negation H' X; rewrite H in H'
| [H : context [?X < ?X] |- _] => by rewrite ltnn in H
| [H : context [?X == ?Y], H' : context [?Y != ?X] |- _] => is_assertion H (X == Y); is_negation H' (Y != X); rewrite eq_sym in H; rewrite H in H'
| [H : context [?X == ?Y], H' : context [?Y < ?X] |- _] => apply (elimT eqP) in H; rewrite H ltnn in H'
| [H : context [?X == ?Y], H' : context [?X < ?Y] |- _] => apply (elimT eqP) in H; rewrite H ltnn in H'
| [H : context [?X < ?Y], H' : context [?Y < ?X] |- _] => let hfalse := fresh in have hfalse : false by rewrite -(ltn_asymmetric X Y) H H' /=
end.


Ltac by_contradiction H := match goal with
| [|- is_true (~~ ?X)] => destruct (X) eqn:H; [|by auto]
| [|- is_true ?X] => destruct (X) eqn:H; [by auto|]
| [|- (~~ ?X) = true] => destruct (X) eqn:H; [|by auto]
| [|- ?X = true] => destruct (X) eqn:H; [by auto|]
| [|- ?X = false] => destruct (X) eqn:H; [|by auto]
end; try mccontradiction.

Ltac by_contra := let H := fresh in by_contradiction H.

Open Scope order_scope.
Theorem strong_induction (p : nat -> Prop) :
p(O) -> (forall n, (forall k, (k <= n -> p(k)) )-> p(n.+1)) -> (forall n, p(n)).
Proof.
move => hp0 hpnk; have h_strong:forall n k:nat,(k <= n -> p(k)).
induction n.
by move => k; rewrite lex0 => /eqP ->.
  move => m; rewrite le_eqVlt => /orP [/eqP ->|]; first by apply hpnk.
  apply IHn.
move => n; apply (h_strong n); done.
Qed.

Ltac strongind X := try generalize dependent X;
match goal with [|- forall X, ?H] => apply (strong_induction (fun X => H)) end;
[|let IHN := fresh "IH" X in intros X IHN].
Tactic Notation "strong" "induction" ident(x) := strongind x.


(* Fixed points of involutions over an {fset K}                               *)

Section Involution_lemma.
Open Scope order_scope.
Open Scope fset_scope.
Open Scope nat_scope.
Variable (K: choiceType).
Definition involution_on (E: {fset K}) (f:K->K) :=
(forall x, x \in E -> f x \in E) /\ (forall x, x \in E -> f (f x) = x).
Definition fixed_fset (E: {fset K}) (f:K->K) :{fset K} := [fset x in E | x==f x].
Definition not_fixed_fset (E: {fset K}) (f:K->K) :{fset K} := E`\`fixed_fset E f.

Lemma sub_invol (E:{fset K}) (f:K->K) (x:K): (involution_on E f)-> (x \in E`\`fixed_fset E f)->
(involution_on (E`\`[fset x; f(x)]) f).
Proof.
move => [HinE Hff] Hin. unfold involution_on. split; intros y Hyin.
have hfy : f y \in E.
 - apply HinE; rewrite in_fsetD in Hyin. by move: Hyin => /andP [_ Hyin].
rewrite in_fsetD; apply /andP. split; [|assumption].
destruct (f y \in [fset x; f x]) eqn: Hfy; [|by []].
rewrite in_fset2 in Hfy. move: Hfy => /orP [/eqP Hfy|/eqP Hfy].
have hyx : y = f x. have hf : f (f y) = f x. by rewrite Hfy.
rewrite -hf Hff. by []. rewrite in_fsetD in Hyin.
by move: Hyin => /andP [_ Hyin]. rewrite <- hyx in Hyin.
rewrite in_fsetD in Hyin. move: Hyin => /andP [Hyin _].
unfold negb in Hyin. rewrite fset22 in Hyin. by [].
have Hf : x = y. rewrite -(Hff x). rewrite -(Hff y).
rewrite Hfy. by []. rewrite in_fsetD in Hyin. by move: Hyin => /andP [_ Hyin].
rewrite in_fsetD in Hin. by move: Hin => /andP [_ Hin].
rewrite in_fsetD in Hyin. move: Hyin => /andP [Hyin _].
unfold negb in Hyin. rewrite Hf in Hyin. by rewrite fset21 in Hyin.
rewrite Hff //. rewrite in_fsetD in Hyin. by move: Hyin => /andP [_ Hyin].
Qed.

Lemma in_fixed_fset {E : {fset K}} (f : K -> K) (x : K) : x \in fixed_fset E f -> x == f x.
Proof. rewrite !inE => /andP. by move => [hE hxfx]. Qed.

Lemma same_fixedset (E:{fset K}) (f:K->K) (x:K):(involution_on E f)-> (x \in E)->(x<>f(x))->
(fixed_fset E f)=(fixed_fset (E`\`[fset x; f(x)]) f).
Proof.
move => hfinv hxE hxfx. apply /eqP. rewrite eqEfsubset.
apply /andP; split; destruct (_ `<=` _) eqn: Hleq; try by [].
  have Hnleq: negb (fixed_fset E f `<=` fixed_fset (E `\` [fset x; f x]) f). by rewrite Hleq.
apply (elimT (fsubsetPn _ _)) in Hnleq. destruct Hnleq as [x' Hin Hnin]. rewrite !inE in Hnin.
rewrite !inE in Hin. repeat rewrite Bool.negb_andb in Hnin. rewrite Bool.negb_involutive in Hnin.
destruct_boolhyp Hin; move => Heq. destruct_boolhyp Hnin.
    reflect_booleq Heq. reflect_booleq Hnin. subst. contradiction.
    reflect_booleq Heq. reflect_booleq Hnin. subst. destruct hfinv as [_ hfinv]. rewrite hfinv in Heq.
symmetry in Heq. by []. by []. unfold negb in Hnin. rewrite Hin in Hnin. by [].
    unfold negb in Hnin. rewrite Heq in Hnin. by [].
  have Hnleq: negb (fixed_fset (E `\` [fset x; f x]) f `<=` fixed_fset E f). by rewrite Hleq.
apply (elimT (fsubsetPn _ _)) in Hnleq. destruct Hnleq as [x' Hin Hnin]. rewrite !inE in Hnin.
rewrite !inE in Hin. repeat rewrite Bool.negb_andb in Hnin. destruct_boolhyp Hin. rewrite Bool.negb_orb in Hin.
destruct_boolhyp Hin; move => Hneq Heq Hin'. destruct_boolhyp Hnin.
    unfold negb in Hnin. by rewrite Hin' in Hnin.
    unfold negb in Hnin. by rewrite Heq in Hnin.
Qed.

Lemma not_fixed (E:{fset K}) (f:K->K) (x:K): (x \in E`\`fixed_fset E f)-> (x <> f(x)).
Proof.
rewrite !inE => /andP => hpred hxfx. move: hxfx hpred => /eqP => hxfx [/negP hnf hxinE].
apply hnf; by rewrite hxfx hxinE.
Qed.

Lemma fsets_equal (A B:{fset K}): (B `<=` A) -> (#|`A`\`B|=0) -> A=B.
Proof.
move => hBsubA hcard0; apply /eqP; rewrite eqEfsubset; apply /andP.
split; last by apply hBsubA.
  - rewrite -fsetD_eq0; apply /eqP; by apply cardfs0_eq.
Qed.

Lemma incl (A B:{fset K}) (x:K): (x \in A`\`B)-> (x \in A).
Proof.
move => hxAB. have hlem:=in_fsetD A B x. rewrite hlem in hxAB.
move: hxAB => /andP; by move=>[ h1 h2].
Qed.

Lemma Involution_lemma (f:K->K): forall (E:{fset K}),
(involution_on E f)-> (odd(#|`(fixed_fset E f)|)=odd(#|`E|)).
Proof.
(* We proceed by strong induction *)
move => E; remember #|`(E`\`(fixed_fset E f))| as n; generalize dependent E.
strong induction n.
   (* Base case: only fixed points *)
 - move => E h_card_notfix _. have h_all_fixed:(E=fixed_fset E f).
   + apply fsets_equal; first by apply fset_sub. by rewrite h_card_notfix.
   by rewrite -h_all_fixed.
  (* Next cases in strong induction *)
 - move => E hSn h_f_inv.
  (* Find an 'x' that is not fixed *)
   + have [x hxEm]: exists x:K, x \in  (E `\` fixed_fset E f).
     apply /fset0Pn; by rewrite -cardfs_gt0 -hSn.
   have hxE:= incl E (fixed_fset E f) x hxEm.
   (* Now remove x and f(x) from E *)
   set F_x := E `\`[fset x; f(x)].
   have h_not_fixed:= not_fixed E f x hxEm.
   have h2:= same_fixedset E f x h_f_inv hxE h_not_fixed.
   have hxfx : x != f x. unfold negb. destruct (x == f x) eqn: Hxfx.
    apply (elimT eqP) in Hxfx. contradiction. by [].
   have hEfx : E = x |` (f x |` F_x). rewrite /F_x -fsetDDl !fsetD1K //.
    rewrite in_fsetD. apply /andP. split.
      unfold negb. rewrite in_fset1. unfold negb in hxfx. rewrite eq_sym in hxfx. by [].
      unfold involution_on in h_f_inv. destruct h_f_inv as [hinv _]. apply hinv in hxE. assumption.
   (* Essential step: the number of non-fixed points has been decreased by 2 *)
   have h_decrease:(n.+1=#|`not_fixed_fset F_x f|.+2).
   + rewrite hSn /not_fixed_fset /F_x. repeat rewrite cardfsDS.
     rewrite cardfs2. rewrite -h2. rewrite hxfx subnAC -cardfsDS; [|by apply fset_sub]. simpl.
     have hadd: (#|` E `\` fixed_fset E f| - 2).+2 = 2 + (#|` E `\` fixed_fset E f| - 2). by [].
     rewrite hadd. rewrite subnKC. by []. apply (@leq_trans (#|` [fset x; f x] |)).
     by rewrite cardfs2 hxfx. apply fsubset_leq_card. rewrite fsubUset. repeat rewrite fsub1set. apply /andP. split.
     by []. rewrite in_fsetD. apply /andP. split. destruct (f x \in (fixed_fset E f)) eqn: Hfff.
     apply in_fixed_fset in Hfff. apply (elimT eqP) in Hfff. rewrite -> Hfff in h_not_fixed. 
     destruct h_f_inv as [_ hinv]. rewrite -> hinv in h_not_fixed; [|by []]. contradiction.
     by []. by apply h_f_inv. rewrite fsubUset. apply /andP; split; rewrite fsub1set. by [].
     by apply h_f_inv. by apply fset_sub. by apply fset_sub.
(* Now we can conclude the induction *)
   have h1: #|`not_fixed_fset F_x f|<=n. inversion h_decrease. done.
   have h_sub_inv:= sub_invol E f x h_f_inv hxEm.
   have h4:= IHn (#|`not_fixed_fset F_x f|) _ F_x. hyp_progress h4; hyp_progress h4.
   have hfxFx : f x \notin F_x. rewrite /F_x in_fsetD Bool.negb_andb. unfold negb. rewrite fset22. by [].
   have hxfxFx : x \notin f x |` F_x. rewrite /F_x -fsetDDl fsetD1K.
   rewrite in_fsetD Bool.negb_andb. unfold negb. rewrite fset11. by [].
   rewrite in_fsetD. apply /andP; split.
   unfold negb. rewrite in_fset1. rewrite eq_sym in hxfx. by [].
   destruct h_f_inv as [hinv _]. apply hinv in hxE. assumption.
   rewrite h2. rewrite -/F_x. rewrite h4. rewrite hEfx. repeat rewrite cardfsU1. rewrite hfxFx hxfxFx. simpl.
  by case (odd #|` F_x|). by [].
Qed.

Lemma odd_existence (A:{fset K}) : odd(#|`A|)-> (exists x:K, x \in A).
Proof.
move => hoddA; apply /fset0Pn. rewrite -cardfs_gt0. by apply odd_gt0.
Qed.

End Involution_lemma.
