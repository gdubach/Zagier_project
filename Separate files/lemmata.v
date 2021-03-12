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
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope fset_scope.
Open Scope nat_scope.

(*  Ad-hoc tactics                                                            *)

Lemma in_Imfset (n m : nat) : (n \in [fsetval x in 'I_m]) <-> (leq (S n) m).
Proof.
split; first by move => /imfsetP /= [x _ ->].
by move => hnp; apply/imfsetP; exists (Sub n hnp).
Qed.

Lemma in_Imfset_r (n m : nat) : (leq (S n) m) -> (n \in [fsetval x in 'I_m]).
Proof.
by apply in_Imfset.
Qed.


Ltac mctocoq := intros; repeat match goal with
| [|- ?X * ?Y <= ?Z * ?W] => apply leq_mul; ((apply ltnW; assumption) || mctocoq; try reflexivity; nia)
| [H : context [_ = false] |- _] => apply (introT negPf) in H
| [H : context [~~ (leq (S _) _)] |- _] => rewrite -leqNgt in H; apply (Bool.reflect_iff _ _ ssrnat.leP) in H; simpl
| [H : context [~~ (leq _ _)] |- _] => rewrite -ltnNge in H; apply (Bool.reflect_iff _ _ ssrnat.leP) in H; simpl
| [H : context [addn] |- _] => unfold addn in H; unfold addn_rec in H; simpl in H
| [H : context [subn] |- _] => unfold subn in H; unfold subn_rec in H; simpl in H
| [H : context [muln] |- _] => unfold muln in H; unfold muln_rec in H; simpl in H
| [H : context [expn] |- _] => unfold expn in H; unfold expn_rec in H; simpl in H
| [H : (leq _ _) = true |- _] => apply (Bool.reflect_iff _ _ ssrnat.leP) in H; simpl
| [H : (leq _ _) = false |- _] => apply (elimF ssrnat.leP) in H; simpl
| [H : context [leq (S _) _] |- _] => apply (elimT ssrnat.ltP) in H; simpl in H
| [H : context [leq _ _] |- _] => apply (elimT ssrnat.leP) in H; simpl in H
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

Ltac mcsimpl := repeat match goal with
| [H : context [_ == _] |- _] => apply (elimT eqnP) in H || apply (elimT eqP) in H
end.

Ltac hyp_progress H := match (type of H) with
| ?X -> ?Y => let Hold := fresh H "old" in rename H into Hold; assert (H : Y); [apply Hold; auto| clear Hold]
end.

Ltac destruct_boolhyp H := repeat (rewrite Bool.negb_andb in H || rewrite Bool.negb_orb in H);
repeat (rewrite -Bool.orb_andb_distrib_r in H || rewrite -Bool.orb_andb_distrib_l in H);
repeat rewrite Bool.negb_involutive in H;
(apply (elimT andP) in H;  let H' := fresh H in destruct H as [H H']; 
  (destruct_boolhyp H' || generalize dependent H'); (destruct_boolhyp H || generalize dependent H))
|| (apply (elimT orP) in H; destruct H as [H | H]; try destruct_boolhyp H).
Ltac reflect_booleq H := apply (elimT eqP) in H.

Ltac is_assertion H X := match (type of H) with
| is_true (X) => rewrite /is_true in H
| X = true => idtac
| ~~ X = false => apply (introT negPf) in H; apply (elimT negPn) in H; rewrite /is_true in H
| true = X => symmetry in H
| false = ~~ X => symmetry in H; apply (introT negPf) in H; apply (elimT negPn) in H; rewrite /is_true in H
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
  rewrite ltnNge leq_eqVlt negb_or in hnm; destruct_boolhyp hnm => hnm hnm'.
  by rewrite hmn in hnm'.
Qed.

Ltac mccontradiction := by (mcsimpl; try subst; contradiction) || by (try subst; match goal with
| [H : ?X = ?Y, H' : ?Y <> ?X |- _] => symmetry in H; contradiction
| [H : ?X = ?Y, H' : ?X <> ?Y |- _] => contradiction
| [H : context [?X < ?X] |- _] => by rewrite ltnn in H
| [H : context [?X == ?Y], H' : context [?Y != ?X] |- _] => (*is_assertion H (X == Y); is_negation H' (Y != X);*) rewrite eq_sym in H; rewrite H in H'
| [H : context [?X == ?Y], H' : context [?Y < ?X] |- _] => apply (elimT eqP) in H; rewrite H ltnn in H'
| [H : context [?X == ?Y], H' : context [?X < ?Y] |- _] => apply (elimT eqP) in H; rewrite H ltnn in H'
| [H : context [?X < ?Y], H' : context [?Y < ?X] |- _] => let hfalse := fresh in have hfalse : false by rewrite -(ltn_asymmetric X Y) H H' /=
| [H : context [?X], H' : context [?X] |- _] => is_assertion H X; is_negation H' X; rewrite H in H'
end).


Ltac by_contradiction H := match goal with
| [|- is_true (~~ ?X)] => destruct (X) eqn:H; [|by auto]
| [|- is_true ?X] => destruct (X) eqn:H; [by auto|]
| [|- (~~ ?X) = true] => destruct (X) eqn:H; [|by auto]
| [|- ?X = true] => destruct (X) eqn:H; [by auto|]
| [|- ?X = false] => destruct (X) eqn:H; [|by auto]
end; try mccontradiction.

Ltac by_contra := let H := fresh in by_contradiction H.

Ltac by_arg_eq := match goal with
| [|- ?F ?X = ?F ?Y] => let H := fresh in have H : X = Y; [|by rewrite H]
end. 

Ltac mcsolve :=
mcsimpl; try subst; (
(by auto) ||
(mcnia) ||
(match goal with 
| [H : context [?X \in ?Y `\` _] |- context [?X \in ?Y]] => rewrite in_fsetD in H;
  destruct_boolhyp H; intros; by (auto || mcnia)
| [H : _ |- ?X] => apply H; mcsolve
end) ||
(repeat (match goal with
| [H : context [_ && _] |- _] => destruct_boolhyp H; intros
| [H : context [_ || _] |- _] => destruct_boolhyp H; intros
end); by (auto || mcnia))) ||
mccontradiction.

Ltac zag_solve := (repeat match goal with
| [|- context [let (X,Y) := ?Z in _]] => destruct Z as [X Y]
| [|- context [if ?X then _ else _]] => case_eq X
| [|- _ -> _] => intros
| [|- (_, _) = (_,_)] => apply pair_eq
| [H : (_, _) = (_,_) |- _] => inversion H; clear H
| [H' : ?X |- context [if ?X then _ else _]] => rewrite H' /=
| [|- _ /\ _] => split
| [|- context [_ && _]] => apply (introT andP)
| [|- context [_ == _]] => apply (introT eqP)
| [H : _ /\ _ |- _] => let H' := fresh H in destruct H as [H H']
| [H : context [_ && _] |- _] => destruct_boolhyp H
| [H : context [_ || _] |- _] => destruct_boolhyp H
end); try apply in_Imfset_r; try mcsolve.

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

Arguments strong_induction p : clear implicits.

Ltac strongind X := try generalize dependent X;
match goal with [|- forall X, ?H] => apply (strong_induction (fun X => H)) end;
[|let IHN := fresh "IH" X in intros X IHN].
Tactic Notation "strong" "induction" ident(x) := strongind x.

Lemma subset_by_in {K : choiceType} (A B : {fset K}) : ~ (exists2 x : K, x \in A & x \notin B) -> A `<=` B.
Proof.
  move => hnot. destruct (_ `<=` _) eqn: hsubset.
  - by [].
  - apply (introT negPf) in hsubset. by apply (elimT (fsubsetPn _ _)) in hsubset.
Qed.


Lemma n_dvdn {p n m : nat} : (n * m == p) -> (dvdn n p).
Proof.
  move => heq. apply (introT dvdnP). exists m. by rewrite mulnC (eqnP heq).
Qed.

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
move => [HinE Hff] Hin. 
unfold involution_on.
split; intros y Hyin.
- have hfy : f y \in E.
  + apply HinE; rewrite in_fsetD in Hyin.
    by move: Hyin => /andP [_ Hyin].
  rewrite in_fsetD; apply /andP.
  split; [|by []].
  by_contradiction Hfy.
  rewrite in_fset2 in Hfy; destruct_boolhyp Hfy; mcsimpl.
  + have hyx : y = f x.
    - replace (f x) with (f (f y)); [| by rewrite Hfy].
      rewrite in_fsetD in Hyin.
      destruct_boolhyp Hyin=> _ Hyin; by rewrite (Hff _ Hyin).
    rewrite in_fsetD in Hyin.
    destruct_boolhyp Hyin => Hyin _.
    by rewrite hyx /negb fset22 in Hyin.
  + have Hf : x = y.
    - rewrite -(Hff x); try mcsolve.
      rewrite -(Hff y); try mcsolve.
      by rewrite Hfy.
    rewrite Hf in_fsetD fset21 in Hyin.
    by auto.
- rewrite Hff //.
  mcsolve.
Qed.

Lemma in_fixed_fset {E : {fset K}} (f : K -> K) (x : K) : x \in fixed_fset E f -> x == f x.
Proof.
rewrite !inE => /andP.
by move => [hE hxfx].
Qed.

Lemma same_fixedset (E:{fset K}) (f:K->K) (x:K):(involution_on E f)-> (x \in E)->(x<>f(x))->
(fixed_fset E f)=(fixed_fset (E`\`[fset x; f(x)]) f).
Proof.
move => hfinv hxE hxfx.
apply /eqP.
rewrite eqEfsubset.
apply /andP; split; by_contradiction Hleq; (apply (introT negPf) in Hleq;
apply (elimT (fsubsetPn _ _)) in Hleq; move: Hleq => [x' Hin Hnin];
rewrite !inE in Hnin, Hin). 
- destruct_boolhyp Hin => Hin Heq.
  destruct_boolhyp Hnin; try mccontradiction.
  + move: hfinv => [_ hfinv]; mcsimpl.
    rewrite Hnin hfinv in Heq; [by mccontradiction | by auto].
  + by rewrite Hin in Hnin.
- destruct_boolhyp Hin => hx'x hx'fx hx'E hx'fx'.
  destruct_boolhyp Hnin ; try mccontradiction.
  + by rewrite hx'E in Hnin.
Qed.

Lemma not_fixed (E:{fset K}) (f:K->K) (x:K): (x \in E`\`fixed_fset E f)-> (x <> f(x)).
Proof.
rewrite !inE => /andP => hpred hxfx.
move: hxfx hpred => /eqP => hxfx [/negP hnf hxinE].
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
by rewrite in_fsetD => h; destruct_boolhyp h.
Qed.

Lemma Involution_lemma (f:K->K): forall (E:{fset K}),
(involution_on E f)-> (odd(#|`(fixed_fset E f)|)=odd(#|`E|)).
Proof.
(* We proceed by strong induction *)
move => E; remember #|`(E`\`(fixed_fset E f))| as n; generalize dependent E.
strong induction n.
   (* Base case: only fixed points *)
 - move => E h_card_notfix _.
   repeat by_arg_eq; symmetry.
   apply fsets_equal.
   + by apply fset_sub.
   + by rewrite h_card_notfix.
  (* Next cases in strong induction *)
 - move => E hSn h_f_inv.
  (* Find an 'x' that is not fixed *)
   have [x hxEm]: exists x:K, x \in  (E `\` fixed_fset E f).
   +  apply /fset0Pn; by rewrite -cardfs_gt0 -hSn.
   have hxE:= incl hxEm.
   (* Now remove x and f(x) from E *)
   set F_x := E `\`[fset x; f(x)].
   have h_not_fixed:= not_fixed hxEm.
   have h_fixed_set_eq:= same_fixedset h_f_inv hxE h_not_fixed.
   have hxfx : x != f x by by_contra.
   have hEfx : E = x |` (f x |` F_x).
   + rewrite /F_x -fsetDDl !fsetD1K // in_fsetD.
     apply /andP; split.
     - rewrite /negb in_fset1.
       by rewrite /negb eq_sym in hxfx.
     - move: h_f_inv => [hinv _].
       by apply hinv in hxE.
   (* Essential step: the number of non-fixed points has been decreased by 2 *)
   have h_decrease:(n.+1 = #|`not_fixed_fset F_x f|.+2).
   + rewrite hSn /not_fixed_fset /F_x.
     repeat rewrite cardfsDS.
     - rewrite cardfs2 -h_fixed_set_eq hxfx subnAC -cardfsDS /=; [|by apply fset_sub].
       rewrite -add2n subnKC; [by []|].
       apply (@leq_trans (#|` [fset x; f x] |)).
       + by rewrite cardfs2 hxfx.
       + apply fsubset_leq_card. rewrite fsubUset !fsub1set.
         apply /andP; split; try mcsolve; rewrite in_fsetD; apply /andP; split.
         - by_contradiction Hfff.
           apply in_fixed_fset in Hfff.
           apply (elimT eqP) in Hfff.
           rewrite -> Hfff in h_not_fixed.
           move: h_f_inv => [_ hinv].
           rewrite hinv in h_not_fixed; mcsolve.
         - mcsolve.
     - rewrite fsubUset. apply /andP; split; rewrite fsub1set; mcsolve.
     - by apply fset_sub.
     - by apply fset_sub.
(* Now we can conclude the induction *)
   have hnfs: #|`not_fixed_fset F_x f|<=n by mcsolve.
   have h_sub_inv:= sub_invol h_f_inv hxEm.
   have IH:= IHn (#|`not_fixed_fset F_x f|) _ F_x.
   do 2 hyp_progress IH.
   have hfxFx : f x \notin F_x by rewrite /F_x in_fsetD Bool.negb_andb /negb fset22.
   have hxfxFx : x \notin f x |` F_x.
   + rewrite /F_x -fsetDDl fsetD1K in_fsetD.
     - by rewrite Bool.negb_andb /negb fset11.
     - apply /andP; split.
       + rewrite /negb in_fset1. 
         by rewrite eq_sym in hxfx.
       + mcsolve.
   rewrite h_fixed_set_eq -/F_x IH.
   + by rewrite hEfx !cardfsU1 hfxFx hxfxFx /= negbK.
   + by [].
Qed.

Lemma odd_existence (A:{fset K}) : odd(#|`A|)-> (exists x:K, x \in A).
Proof.
move => hoddA; apply /fset0Pn.
rewrite -cardfs_gt0.
by apply odd_gt0.
Qed.

End Involution_lemma.