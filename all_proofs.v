(*                                                                            *)
(*    This file contains the full proofs of Fermat's two squares Theorem      *)
(*                              also known as Fermat's Christmas Theorem      *)
(*                               by Guillaume Dubach and Fabian Mühlböck      *)
(*                                                     IST Austria, 2021      *)
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

Lemma in_Imfset_eq {n m : nat} : (n \in [fsetval x in 'I_m]) = leq (S n) m.
Proof.
destruct (_ < _) eqn: hlt.
- by apply in_Imfset in hlt.
- destruct (_ \in _) eqn: hin.
  + apply in_Imfset in hin.
    by rewrite hin in hlt.
  + by [].
Qed.

Ltac mcsimpl := repeat match goal with
| [H : context [_ == _] |- _] => apply (elimT eqnP) in H || apply (elimT eqP) in H
| [H: context [Imfset.imfset _ _ _] |- _] => rewrite !in_Imfset_eq in H
end.

Ltac mctocoq := intros; mcsimpl; try rewrite !in_Imfset_eq; repeat match goal with
| [|- ?X * ?Y <= ?Z * ?W] => apply leq_mul; ((apply ltnW; assumption) 
                             || mctocoq; try reflexivity; nia)
| [H : context [_ = false] |- _] => apply (introT negPf) in H
| [H : context [~~ (leq (S _) _)] |- _] => rewrite -leqNgt in H; 
                             apply (Bool.reflect_iff _ _ ssrnat.leP) in H; simpl
| [H : context [~~ (leq _ _)] |- _] => rewrite -ltnNge in H; 
                             apply (Bool.reflect_iff _ _ ssrnat.leP) in H; simpl
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
(mcsimpl; try subst; (
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
end); by (auto || mcnia)))) ||
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
| [H : context [_ \/ _] |- _] => apply (introT orP) in H; destruct_boolhyp H
| [H : context [_ /\ _] |- _] => apply (introT andP) in H; destruct_boolhyp H
end); repeat rewrite -> in_Imfset_eq; try mcsolve.

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
 - apply (introT negPf) in hsubset; by apply (elimT (fsubsetPn _ _)) in hsubset.
Qed.


Lemma n_dvdn {p n m : nat} : (n * m == p) -> (dvdn n p).
Proof.
move => heq. apply (introT dvdnP). exists m. by rewrite mulnC (eqnP heq).
Qed.

(* Fixed points of involutions over an {fset K}                               *)

Section Involution_Lemma.
Open Scope order_scope.
Open Scope fset_scope.
Open Scope nat_scope.
Variable K: choiceType.
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

Lemma involution_lemma (f:K->K): forall (E:{fset K}),
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

End Involution_Lemma.
Check involution_lemma.

(*                                                                            *)
(*  Formal proof of Fermat's Theorem, following Zagier's one-sentence proof.  *)
(*                                                                            *)
(*  This proof is from:                                                       *)
(*  D. Zagier, A One-Sentence Proof That Every Prime p $\equiv$ 1 (mod 4)     *)
(*  is a Sum of Two Squares,                                                  *)
(*                The American Mathematical Monthly 97 (1990), no.2, 144-144. *)
(*                                                                            *)

Section Zagier_Proof.
Open Scope nat_scope.

Variable p:nat.
Variable p_prime : prime p.

Definition N3 : Type := nat * nat * nat.
Definition involutionN3:= (@involution_on [choiceType of N3]).
Definition fixed_fsetN3:=(@fixed_fset [choiceType of N3]).
Definition involutionN3_lemma:=(@involution_lemma [choiceType of N3]).
Definition Ipfset:{fset nat} := [fsetval n in 'I_p].
Definition Ipf3:{fset N3} := (Ipfset`*`Ipfset`*`Ipfset).
Definition area (t:N3) :nat := (t.1.1)^2+4*(t.1.2)*(t.2).
Definition S:{fset N3} := [fset t:N3 | t \in Ipf3 & (p == area(t))].
Definition zig (t : N3) :N3 := (t.1.1, t.2, t.1.2).
Definition zag (t:N3) :N3 := match t with (x,y,z) =>
 if y >= (x+z) then (x+2*z,z,y-(x+z))
    else if (2*y) >= x then (2*y-x,y,z+x-y)
         else (x-2*y,z+x-y,y) end.

(*  Basic properties                                                          *)

Lemma modulo_ex: ((modn p 4) = 1) -> (exists k, p=k*4+1).
Proof.
by move => h_pmod4; exists (p%/4); rewrite{1} (divn_eq p 4) h_pmod4.
Qed.

Lemma square_eq : forall n : nat, n * n == n -> (n == 1) || (n == 0).
Proof.
move => n /eqP hnn.
by have [->|->]:(n = 1) \/ (n = 0) by mcnia.
Qed.

Lemma _2_div_p : (2 %|p) -> (2 = p).
Proof.
move => h2p; apply/eqP.
by rewrite -(dvdn_prime2 _ p_prime).
Qed.

Lemma _4_div_p : (4 %|p) -> False.
Proof.
move => h4p.
have /_2_div_p h2p: 2%|p by apply (@dvdn_trans 4 2 p).
by move: h4p; rewrite - h2p.
Qed.

Lemma area_x (x y z : nat) : p=area (x,y,z) -> ~(x = 0).
Proof.
rewrite /area => har h0; move: h0 har => -> /=.
rewrite (expnD 0 1 1) (expn1 0) muln0 add0n.
rewrite -mulnA => har; apply:  _4_div_p; rewrite har.
by apply /eqP; rewrite modnMr.
Qed.

Lemma area_yz (x y z : nat) : p=area (x,y,z) -> ~((y = 0)\/(z = 0)).
Proof.
have [Hp hpfa]:=(primeP p_prime).
rewrite /area => har [h0|h0]; move: har; rewrite h0 /= muln0 ?mul0n addn0=> har;
have [/eqP hxp|/eqP hxp] :  (x == 1) \/ (x == p)
  by apply/orP; apply:hpfa ; rewrite har -mulnn /dvdn modnMr.
- by move: har Hp; rewrite hxp exp1n => -> .
- by move/eqP: har Hp; rewrite hxp eq_sym=> /square_eq/orP [/eqP -> | /eqP ->] //=.
- move: har Hp;  rewrite hxp => -> //=.
- move/eqP: har Hp;  rewrite hxp eq_sym=> /square_eq/orP  [/eqP -> | /eqP ->] //=.
Qed.

Lemma area_p (x y z : nat) : p = area (x,y,z) -> x > 0 /\ y > 0 /\ z > 0.
Proof.
move => harea; split; move: harea; first by move/area_x => /eqP //=; rewrite lt0n.
move/area_yz=> H; split; rewrite lt0n; apply/negP => /eqP h; move: H; rewrite h.
- by apply; left.
- by apply; right.
Qed.

Lemma area_p_xy (x y z : nat) : p = area (x,y,z) -> x = y -> x = 1 /\ y = 1.
Proof.
rewrite /area /= => har heq.
have [Hx [Hy Hz]]:=(area_p har).
have hxnp:x<>p.
- move=> hxep; rewrite hxep in har.
  have Hbad: p ^ 2 + 4 * y * z > p by mcnia.
  rewrite {1} har in Hbad.
  by move: Hbad; rewrite ltn_neqAle=> /andP [/eqP Hbad _]; apply: Hbad.
rewrite -heq expnSr mulnC (mulnC 4 x) -mulnA in har.
have [_ divp] := primeP p_prime.
have [/eqP hyes |/eqP hno] : (x == 1) \/ (x == p).
- apply/orP; apply: divp.
  by rewrite /dvdn har /expnSr -modnDm !modnMr addn0 mod0n.
- by split; first by []; rewrite -heq.
by exfalso.
Qed.

Lemma bound_Sp: forall (t:N3), p = area t ->  t.1.1<p /\ t.1.2<p /\ t.2<p.
Proof.
move => [[x y] z] ; rewrite /area /= => Harea.
have [/= Hxn0 [Hyn0 Hzn0]] := area_p Harea.
split; [|split]; by_contradiction hcontra => //=;
  rewrite Harea in hcontra; rewrite -hcontra; mcnia.
Qed.

(* Study of the zig involution                                                *)

Lemma zig_involution: involutionN3 S zig.
Proof.
rewrite /involution_on; split; move => [[x y] z]; rewrite !inE /zig /area /= => h;
  zag_solve.
Qed.

Lemma zig_solution (t:N3):
  (t \in fixed_fset S zig)->(exists a b: nat, p=a^2+b^2).
Proof.
rewrite !inE /area /zig => htfix; destruct_boolhyp htfix => hx hy hz hp _ ht _.
rewrite /= in ht.
exists t.1.1; exists (2*(t.2)).
mcnia.
Qed.

(* Study of the zag involution                                                *)

Lemma zag_involution: involutionN3 S zag.
Proof.
rewrite /involution_on; split; move => [[x y] z].
 - rewrite !inE /area /zag /Ipfset /= /area /zag => hin.
   destruct_boolhyp hin => hx hy hz /eqP hp.
   have harea_p := area_p hp.
   zag_solve.
 - rewrite !inE /zag => htS; destruct_boolhyp htS => hx hy hz /eqP hp.
   have harea_p := area_p hp.
   zag_solve.
Qed.

Lemma zag_fixed_point (k:nat): (p = k*4+1) -> (fixed_fsetN3 S zag)=[fset (1,1,k)].
Proof.
move => h_pmod4; apply/eqP; rewrite eqEfsubset; apply/andP; split.
 - apply/fsubsetP => t; move: t=>[[x y] z] /=.
   rewrite !inE /zag /=.
   move => hp; destruct_boolhyp hp => /= hx hy hz /eqP hp hxe.
   have [hx0 [hy0 hz0]] := area_p hp.
   have hxy := (area_p_xy hp); hyp_progress hxy; generalize dependent hxe; zag_solve.
   rewrite /area in hp; simpl in *.
   zag_solve.
 - apply/fsubsetP => x; rewrite !inE => /eqP -> /=.
   have harea : p=area (1,1,k) by rewrite/area h_pmod4 /=; ring.
   have [/= hbx [_ hbz]] := bound_Sp harea.
   repeat (apply/andP; split); try apply/in_Ipfset; zag_solve => //=.
Qed.

(*                                                                            *)
(*  Zagier's proof                                                            *)
(*  (Zagier's 'one-sentence' is given as comments)                            *)
(*                                                                            *)

Theorem Fermat_Zagier : p %% 4 = 1 -> exists a b :nat, p=a^2 + b^2.
Proof.
move /modulo_ex => [k hk].
(* 'The involution on the finite set [S] defined by [zag]'                    *)
have h_zag_invol:=zag_involution.
(* 'has exactly one fixed point,'                                             *)
have h_zag_fix_card:(#|`(fixed_fsetN3 S zag)|) = 1.
   - by rewrite (zag_fixed_point hk); first by apply: cardfs1.
(* 'so |S| is odd,'                                                           *)
have h_S_odd: odd(#|`S|).
   by rewrite -(involutionN3_lemma h_zag_invol) h_zag_fix_card.
(* 'and the involution defined by [zig].'                                     *)
have h_zig_invol:= zig_involution.
(* 'also has a fixed point.'                                                  *)
have [t htzigfix]: exists t:N3, t \in (fixed_fsetN3 S zig).
  by apply odd_existence; rewrite (involutionN3_lemma h_zig_invol).
by apply (zig_solution htzigfix).
Qed.

End Zagier_Proof.
Check Fermat_Zagier.

(*                                                                            *)
(*     Another proof of Fermat's Theorem, using partitions of integers        *)
(*  This proof is from:                                                       *)
(*    A. David Christopher                                                    *)
(*    A partition-theoretic proof of Fermat’s Two Squares Theorem             *)
(*    Discrete Mathematics 339 (2016), no. 4, 1410-1411.                      *)
(*                                                                            *)

Section Partition_Proof.
Open Scope fset_scope.
Open Scope nat_scope.

Variable p:nat.
Variable p_prime : prime p.

Definition Ip:{fset nat} := [fsetval n in 'I_p].
Definition N4 : Type := (nat * nat) * (nat * nat).
Definition Ip4:{fset N4} := ((Ip`*`Ip)`*`(Ip`*`Ip)).
Definition involutionN4:= (@involution_on [choiceType of N4]).
Definition fixed_fsetN4:=(@fixed_fset [choiceType of N4]).
Definition involutionN4_lemma:=(@involution_lemma [choiceType of N4]).

(* Y_area is the area of a Young diagram                                      *)
Definition Y_area (yd : N4) : nat := yd.1.1*yd.1.2+yd.2.1*yd.2.2.

Definition P2p :=[fset yd:N4 | (yd \in Ip4) && ((Y_area yd ==p)&&(yd.1.1>yd.2.1))].
  Definition P2p_l :=[fset yd:N4 | (yd \in P2p) && (yd.1.2<yd.2.2)].
  Definition P2p_e :=[fset yd:N4 | (yd \in P2p) && (yd.1.2==yd.2.2)].
  Definition P2p_g :=[fset yd:N4 | (yd \in P2p) && (yd.1.2>yd.2.2)].

(* Basic properties                                                           *)

Lemma Ip4_not_p_factors (a f : nat): a \in Ip -> f \in Ip -> ~ (a * f == p).
Proof.
move => ha hf.
apply (elimT negP).
by_contradiction hassume.
  have hda : a %| p by rewrite /dvdn -(eqnP hassume) modnMr.
  have hdf : f %| p by rewrite /dvdn -(eqnP hassume) modnMl.
  have [hp hdiv] := (primeP p_prime).
  apply hdiv in hda,hdf.
  rewrite /Ip in ha,hf.
  zag_solve.
Qed.

Lemma area_gt0_all : forall yd : N4, (yd \in Ip4) -> Y_area yd == p 
-> (yd.1.1 > 0)/\(yd.1.2>0)/\(yd.2.1>0)/\(yd.2.2>0).
Proof.
move => [[a1 f1] [a2 f2]] hin harea.
rewrite !inE in hin.
rewrite /Y_area /= in harea.
destruct_boolhyp hin => /= hina1 hinf1 hina2 hinf2.
repeat split; by_contradiction hc; exfalso; 
  apply (introT negPf) in hc; rewrite -leqNgt leqn0 in hc;
  rewrite (eqnP hc) in harea;
  rewrite ?mul0n ?muln0 ?add0n ?addn0 in harea;
  unshelve eapply (Ip4_not_p_factors _ _ harea); by [].
Qed.

Lemma P2p_in_Ip4 (yd:N4): (yd \in P2p)-> (yd \in Ip4).
Proof.
rewrite inE; by rewrite inE => /andP [hinI4 _].
Qed.

(* Study of P2p via conjugation                                               *)

Definition conjugate (a : N4) : N4:= ((a.1.2 + a.2.2,a.2.1),(a.1.2,a.1.1-a.2.1)).

Lemma conjugate_involution : involutionN4 P2p conjugate.
Proof.
split.
 - move => yd hin.
   have hinI4 := (@P2p_in_Ip4 yd hin).
   rewrite !inE in hin.
   destruct_boolhyp hin => hina1 hinf1 hina2 hinf2 harea hleq.
   have [ha1 [hf1 [ha2 hf2]]] := (@area_gt0_all yd hinI4 harea).
   rewrite /conjugate !inE /Y_area.
   rewrite /Y_area in harea.
   zag_solve.
 - move => [[a1 f1] [a2 f2]] hin; rewrite !inE in hin.
   destruct_boolhyp hin => hina1 hinf1 hina2 hinf2 _.
   rewrite /conjugate.
   zag_solve.
Qed.

Lemma conjugate_fixed : (modn p 4  = 1) -> #|`fixed_fsetN4 P2p conjugate| = 1.
Proof.
move /modulo_ex => [k hk].
have h_singleton : fixed_fsetN4 P2p conjugate = [fset ((2*k+1,1),(1,2*k))].
- apply/eqP; rewrite eqEfsubset; apply/andP; split;
  apply/fsubsetP => yd; rewrite !inE /conjugate; move: yd=>[[a1 f1] [a2 f2]] /= h.
  + destruct_boolhyp h => /= ha1 hf1 ha2 hf2 harea hlt heq hf1a2 ha2f1 hf2a1a2.
    mcsimpl; subst; rewrite /Y_area /= in harea.
    have harea' : a2 * (a2 + f2 + f2) == p by mcnia.
    have hdvdn := (n_dvdn harea').
    have ha2_1: a2 = 1.
    - have p_prime' := p_prime; apply (elimT primeP) in p_prime'.
      destruct p_prime' as [_ hdiv]; apply hdiv in hdvdn.
      by destruct_boolhyp hdvdn; mcnia.
    zag_solve.
  + move: h => /eqP [ha1 hf1 ha2 hf2].
    rewrite ha1 hf1 ha2 hf2 /Y_area.
    have kgt0 : k > 0.
    - by_contradiction hkgt0.
      have hk0: (k = 0) by mcnia.
      have p_prime' := p_prime; apply (elimT primeP) in p_prime'.
      mccontradiction.
    zag_solve.
rewrite h_singleton; by rewrite cardfs1.
Qed.

Lemma P2p_odd :  (modn p 4  = 1) -> odd(#|`P2p|).
Proof.
rewrite -(@involutionN4_lemma conjugate P2p conjugate_involution).
move => hp4.
by rewrite conjugate_fixed.
Qed.

(* Study of P2p_l via double transposition                                    *)

Definition transpose_l (a : N4) : N4:= ((a.2.2,a.2.1),(a.1.2,a.1.1)).

Lemma transpose_l_involution : involutionN4 P2p_l transpose_l.
Proof.
split.
 - move => [[a1 f1] [a2 f2]].
   rewrite !inE /Y_area /transpose_l.
   zag_solve.
 - move => [[a1 f1] [a2 f2]].
   rewrite !inE /transpose_l.
   zag_solve.
Qed.

Lemma transpose_l_fixed : #|`fixed_fsetN4 P2p_l transpose_l| = 0.
Proof.
have heq0 : fixed_fsetN4 P2p_l transpose_l = fset0; [|by rewrite heq0].
apply (elimT eqP).
rewrite /fixed_fsetN4 /fixed_fset -fsubset0.
by_contradiction hsubset.
apply (introT negPf) in hsubset.
apply (elimT (fsubsetPn _ _)) in hsubset.
move: hsubset => [[[a1 f1] [a2 f2]] hin _].
rewrite !inE in hin.
destruct_boolhyp hin => /= ha1 hf1 ha2 hf2 harea ha2a1 hf1f2 ha1f2 hf1a2 _ _.
rewrite /Y_area /= in harea.
mcsimpl; subst.
have p_prime' := p_prime. apply (elimT primeP) in p_prime'.
move: p_prime' => [hp1 hdvdnp].
have harea' :  2 * (a2 * f2) == p by mclia.
have h2divp := (n_dvdn harea').
apply hdvdnp in h2divp.
rewrite /= in h2divp.
have ha2_1 : a2 = 1 by mcnia.
have hf2_1 : f2 = 1 by mcnia.
by rewrite ha2_1 hf2_1 ltnn in ha2a1.
Qed.

Theorem P2p_l_even : ~~odd(#|`P2p_l|).
Proof.
rewrite -(@involutionN4_lemma transpose_l P2p_l transpose_l_involution).
by rewrite transpose_l_fixed.
Qed.

(* Study of P2p_e via enumeration                                             *)

Lemma mod4_halfeven : (modn p 4  = 1) -> (divn (p - 1) 2) %% 2 == 0.
Proof.
apply (elimT primeP) in p_prime.
move: p_prime => [hp1 hdvdn] hpmod.
have hp: (p - 1).+1 = p by mcnia.
have hp1mod : (p-1) %% 4 = 0.
- rewrite subn1 modn_pred; [|by []| auto;fail].
  by rewrite hpmod /= /dvdn hpmod /=.
by rewrite modn_divl /muln /= hp1mod div0n.
Qed.

Definition P2p_e_mapfun : nat -> N4 := fun x : nat => ((p - (x + 1), 1), (x + 1, 1)). 

Lemma P2p_e_I_map : P2p_e = [fset (P2p_e_mapfun x) | x in [fsetval y in 'I_((divn (p - 1) 2))]].
Proof.
have p_prime' := p_prime. 
apply (elimT primeP) in p_prime'.
move: p_prime' => [hp1 hprime].
apply /eqP.
(* unfold definitions and assert set equality by mutual subset relationship *)
rewrite /P2p_e /P2p /P2p_e_mapfun eqEfsubset.
(* both subset relationships hold because there exists no element in
   the subset that does not exist in the superset.
   both proofs eventually rely on the fact that p > 2, and therefore
   p - 1 must be even. *)
apply /andP; split; 
  apply subset_by_in; 
  move => [[[a1 f1] [a2 f2]] hin hnin];
  apply (elimT negP) in hnin; apply hnin; clear hnin.
  (* the first case is the easier one; the hard part is
     to prove that (a2 - 1) < floor((p - 1)/2).
     First, however, we collect some facts and prove that f1 = f2 = 1*)
- rewrite !inE /Ip /= in hin.
  destruct_boolhyp hin => /= ha1 hf1 ha2 hf2 harea ha2a1 hf1f2.
  have hgt0 := (@area_gt0_all ((a1,f1),(a2,f2)) _ harea).
  hyp_progress hgt0; [by rewrite /Ip4 !inE; zag_solve|].
  move: hgt0 => /= [ha1_0 [hf1_0 [ha2_0 hf2_0]]].
  rewrite (eqnP hf1f2) /Y_area /= in harea.
  rewrite (eqnP hf1f2).
  clear hf1f2 hf1 hf1_0 f1.
  have hf2_1 : f2 = 1.
  + replace (a1 * f2 + a2 * f2) with (f2 * (a1 + a2)) in harea; [|by ring].
    apply (n_dvdn) in harea.
    apply hprime in harea.
    zag_solve.
  rewrite hf2_1.
  rewrite hf2_1 !muln1 in harea.
  clear hf2_1 hf2 hf2_0 f2.
  (* Now it is easy to see that the way to instantiate
     x to satisfy the membership goal is by (a2 - 1), which means we
     need to prove that (a2 - 1) < (p - 1) % 2 *)
  apply /imfsetP; exists (a2 - 1); [|zag_solve].
  apply/imfsetP; unshelve (eexists (Sub (a2 - 1) _)).
  (* the following fact (relying on the knowledge that p-1 is even) 
     helps mcnia figure out that the inequation holds *)
  + have hp : p - 1 = 2 * ((p - 1) %/ 2).
    - have hpgt2 : p > 2 by mcnia.
      apply (elimT eqP).
      rewrite mulnC eq_sym -dvdn_eq dvdn2 -oddS subn1 -Lt.S_pred_pos; [|by mcsolve].
      apply even_prime in p_prime.
      case p_prime; zag_solve.
    mcnia.
  + zag_solve.
  + zag_solve.
  (* the second part is the more complicated one; it again
     relies on the fact that p > 2 and therefore odd.
     This in turn means that we can prove the inequality
     2 * (x + 1) < p by weakening the inequality to <=
     and proving that the equal-case cannot hold as the LHS
     is even, but p is odd.
     *)
- rewrite !inE /=.
  apply (elimT (imfsetP _ _ _ _)) in hin.
  move: hin => [x hin heq].
  inversion heq; subst; clear heq.
  apply in_Imfset in hin.
  have hxp : 2 * x < (p - 2).
  + have hpgt2 : p > 2.
    - by_contradiction hcontra.
      have hp2: p = 2 by mclia.
      mccontradiction.
    have pdiv2 : 2 %| (p - 1).
    - apply even_prime in p_prime.
      rewrite dvdn2 oddB; zag_solve.
      destruct p_prime as [hp|hp]; try rewrite hp; zag_solve.
    rewrite ltn_subRL.
    replace (2 + 2 * x) with (2 * (x + 1)); [|by mclia].
    (* now turn < into != && <= *)
    rewrite ltn_neqAle.
    apply /andP; split.
    (* != holds because even != odd *)
    - by_contradiction hcontra.
      rewrite dvdn2 -oddS subn1 -Lt.S_pred_pos -(eqP hcontra) in pdiv2; [|by mclia].
      by rewrite oddM /= in pdiv2.
    (* <= holds by hin and p-1's evenness *)
    - rewrite ltn_divRL in hin; zag_solve.
  (* the fact that 2 * x < (p - 2) suffices to solve the rest *)
  rewrite /Y_area; zag_solve.
Qed.

Lemma Pdp_e_card_pairs : #|`P2p_e| = (divn (p - 1) 2).
Proof.
rewrite P2p_e_I_map !card_imfset /=.
- by rewrite -cardE card_ord.
- rewrite /injective => x1 x2 h.
  by apply ord_inj in h.
- move => x1 x2 h.
  apply /eqP.
  by_contradiction heq.
  rewrite /P2p_e_mapfun in h.
  apply (introT eqP) in h.
  rewrite !xpair_eqE in h.
  have hx1x2 : x1 == x2 by zag_solve.
  mccontradiction.
Qed.

Lemma Pdp_e_card :  (modn p 4  = 1) -> ~~odd(#|`P2p_e|).
Proof.
move => hmod.
rewrite Pdp_e_card_pairs.
apply mod4_halfeven in hmod.
by rewrite -eqb0 -modn2.
Qed.

Lemma card_disjoint_triple {K : choiceType} (A B C : {fset K}) : A `&` B = fset0 -> A `&` C = fset0 -> B `&` C = fset0 -> #|` A `|` B `|` C | = #|` A | + #|` B | + #|` C |.
Proof.
move => hab hac hbc.
have hui1 := (cardfsUI (A `|` B) C).
have hui2 := (cardfsUI A B).
rewrite hab cardfs0 addn0 in hui2.
rewrite hui2 in hui1.
by rewrite -hui1 fsetIUl hac hbc fsetU0 cardfs0 addn0.
Qed.

Lemma P2p_partition: #|`P2p|=#|`P2p_l|+#|`P2p_e|+#|`P2p_g|.
Proof.
have hunion : P2p = P2p_l `|` P2p_e `|` P2p_g.
- apply /eqP.
  rewrite eqEfsubset.
  apply /andP; split; apply subset_by_in; move => [[[a1 f1] [a2 f2]] hin hnin].
  + rewrite !inE /= in hin.
    rewrite !in_fsetU !Bool.negb_orb !inE !Bool.negb_andb /= in hnin.
    destruct_boolhyp hin => /= ha1 hf1 ha2 hf2 harea ha2a1.
    destruct_boolhyp hnin; try mccontradiction; move => hx1 hx2 hx3.
    rewrite -leqNgt leq_eqVlt in hx1.
    zag_solve.
  + rewrite !inE !Bool.negb_andb /= in hnin.
    rewrite !in_fsetU !inE /= in hin.
    destruct_boolhyp hin => /= ha1 hf1 ha2 hf2 harea ha2a1;
    destruct_boolhyp hnin; mccontradiction.
- rewrite hunion.
  by apply card_disjoint_triple;
    apply (elimT eqP); rewrite fsetI_eq0; apply /fdisjointP; 
    move => [[a1 f1] [a2 f2]] hin; rewrite !inE /Y_area /= in hin; 
    rewrite !inE /Y_area /=; apply (introT negP); move => hnin;
    destruct_boolhyp hin; destruct_boolhyp hnin; intros; mccontradiction.
Qed.

Lemma P2p_g_odd : (modn p 4  = 1) -> odd #|` P2p_g |.
move => hmod.
have hodd := P2p_odd hmod.
rewrite P2p_partition !oddD in hodd.
by rewrite (negPf P2p_l_even) (negPf (Pdp_e_card hmod)) /= in hodd.
Qed.

(* Study of P2p_g via simple transposition                                    *)

Definition transpose_g (a : N4) : N4:= ((a.1.2,a.1.1),(a.2.2,a.2.1)).

Lemma transpose_g_involution : involutionN4 P2p_g transpose_g.
Proof.
split.
- move => yd hin; rewrite !inE /Y_area in hin.
  rewrite /transpose_l !inE /Y_area.
  zag_solve.
- move => [[a1 f1] [a2 f2]] hin; rewrite !inE /Y_area in hin.
  rewrite /transpose_g.
  zag_solve.
Qed.

Lemma transpose_g_fixed : (exists (yd:N4), (yd \in (fixed_fsetN4 P2p_g transpose_g)))
                                 -> (exists a b :nat, p=a^2 + b^2).
Proof.
move => [[[a1 f1] [a2 f2]] hin] /=.
exists a1; exists a2.
rewrite !inE /transpose_g /Y_area /= in hin.
destruct_boolhyp hin => /=; intros.
mcnia.
Qed.

(*                                                                            *)
(* Proof of Fermat's theorem using partitions, following David Christopher    *)
(*                                                                            *)

Theorem Fermat_David_Christopher : p %% 4 = 1 -> exists a b :nat, p=a^2 + b^2.
Proof.
move => hk.
apply transpose_g_fixed.
apply odd_existence. 
rewrite involution_lemma.
- by apply P2p_g_odd.
- by apply transpose_g_involution.
Qed.

End Partition_Proof.
Check Fermat_David_Christopher.

(*                                                                            *)
(*               End of the proofs of Fermat's Theorem                        *)
(*                                                                            *)