   (**                                                                        **
 *    This file contains the full proofs of Fermat's two squares Theorem    *
 *                              also known as Fermat's Christmas Theorem    *
 *                               by Guillaume Dubach and Fabian Mühlböck    *
 *                                                     IST Austria, 2021    *
 **                                                                        **)

From mathcomp Require Import all_ssreflect ssrbool ssrnat eqtype ssrfun ssralg seq.
From mathcomp Require Import choice path finset finfun fintype bigop finmap.
From mathcomp Require Import order.
Require Import Psatz.
Import Order.TTheory GRing.Theory.
Set Implicit Argument.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope fset_scope.
Open Scope nat_scope.

(** Ad-hoc tactics **)

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

(* Two examples of uses of mcnia on remarkable identities for nat type *)

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


Ltac hyp_progress H := match (type of H) with
| ?X -> ?Y => let Hold := fresh H "old" in rename H into Hold; assert (H : Y); [apply Hold; auto| clear Hold]
end.

Ltac destruct_boolhyp H := try (apply (elimT eqP) in H); (apply (elimT andP) in H; 
let H' := fresh H in destruct H as [H H']; try destruct_boolhyp H; try destruct_boolhyp H'; generalize dependent H')
|| (apply (elimT orP) in H; destruct H as [H | H]; try destruct_boolhyp H).
Ltac reflect_booleq H := apply (elimT eqP) in H.

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

(** Fixed points of involutions over an {fset K} **)

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
 + apply HinE; rewrite in_fsetD in Hyin. by move: Hyin => /andP [_ Hyin].
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
  + rewrite -fsetD_eq0; apply /eqP; by apply cardfs0_eq.
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
 + move => E h_card_notfix _. have h_all_fixed:(E=fixed_fset E f).
   - apply fsets_equal; first by apply fset_sub. by rewrite h_card_notfix.
   by rewrite -h_all_fixed.
  (* Next cases in strong induction *)
 + move => E hSn h_f_inv.
  (* Find an 'x' that is not fixed *)
   - have [x hxEm]: exists x:K, x \in  (E `\` fixed_fset E f).
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
   - rewrite hSn /not_fixed_fset /F_x. repeat rewrite cardfsDS.
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

(** Formal proof of Fermat's Theorem, following Zagier's one-sentence proof **)

Section Zagier_proof.
Open Scope nat_scope.
Variable p:nat.
Variable p_prime : prime p.
Definition N3 : Type := nat * nat * nat.
Definition involutionN3:= (involution_on [choiceType of N3]).
Definition fixed_fsetN3:=(fixed_fset [choiceType of N3]).
Definition InvolutionN3_lemma:=(Involution_lemma [choiceType of N3]).
Definition Ipfset:{fset nat} := [fsetval n in 'I_p].
Definition Ipf3:{fset N3} := (Ipfset`*`Ipfset`*`Ipfset).
Definition area (t:N3) :nat := (t.1.1)^2+4*(t.1.2)*(t.2).
Definition S:{fset N3} := [fset t:N3 | t \in Ipf3 & (p==area(t))].
Definition zig (t : N3) :N3 := (t.1.1, t.2, t.1.2).
Definition zag (t:N3) :N3 := match t with (x,y,z) =>
 if y >= (x+z) then (x+2*z,z,y-(x+z))
    else if (2*y) >= x then (2*y-x,y,z+x-y)
         else (x-2*y,z+x-y,y) end.

(** Basic properties **)

Lemma modulo_ex: ((modn p 4) = 1) -> (exists k, p=k*4+1).
Proof. by move => h_pmod4; exists (p%/4); rewrite{1} (divn_eq p 4) h_pmod4. Qed.

Lemma in_Ipfset (n : nat) : (n \in Ipfset) <-> (n<p).
Proof.
split; first by rewrite /Ipfset => /imfsetP /= [x _ ->].
by move => hnp; apply/imfsetP; exists (Sub n hnp).
Qed.

Lemma square_eq : forall n : nat, n * n == n -> (n == 1) || (n == 0).
Proof.
move => n /eqP hnn. by have [->|->]:(n = 1) \/ (n = 0) by mcnia.
Qed.

Lemma _2_div_p : (2 %|p) -> (2 = p).
Proof. move => h2p; apply/eqP. by rewrite -(dvdn_prime2 _ p_prime). Qed.

Lemma _4_div_p : (4 %|p) -> False.
Proof.
move => h4p. have /_2_div_p h2p: 2%|p by apply (@dvdn_trans 4 2 p).
by move: h4p; rewrite - h2p.
Qed.

Lemma area_x (x y z : nat) : p=area (x,y,z) -> ~(x = 0).
Proof.
rewrite /area => har h0; move: h0 har => -> /=. rewrite (expnD 0 1 1) (expn1 0) muln0 add0n.
rewrite -mulnA => har; apply:  _4_div_p; rewrite har. by apply /eqP; rewrite modnMr.
Qed.

Lemma area_yz (x y z : nat) : p=area (x,y,z) -> ~((y = 0)\/(z = 0)).
Proof.
have [Hp hpfa]:=(primeP p_prime).
rewrite /area => har [h0|h0]; move: har; rewrite h0 /= muln0 ?mul0n addn0=> har;
have [/eqP hxp|/eqP hxp] :  (x == 1) \/ (x == p)
  by apply/orP; apply:hpfa ; rewrite har -mulnn /dvdn modnMr.
by move: har Hp; rewrite hxp exp1n => -> .
move/eqP: har Hp; rewrite hxp eq_sym=> /square_eq/orP [/eqP -> | /eqP ->] //=.
move: har Hp;  rewrite hxp => -> //=.
move/eqP: har Hp;  rewrite hxp eq_sym=> /square_eq/orP  [/eqP -> | /eqP ->] //=.
Qed.

Lemma area_p (x y z : nat) : p = area (x,y,z) -> x > 0 /\ y > 0 /\ z > 0.
Proof.
move => harea; split; move: harea; first by move/area_x => /eqP //=; rewrite lt0n.
move/area_yz=> H; split; rewrite lt0n; apply/negP => /eqP h; move: H; rewrite h.
  by apply; left. by apply; right.
Qed.

Lemma area_p_xy (x y z : nat) : p = area (x,y,z) -> x = y -> x = 1 /\ y = 1.
Proof.
rewrite /area /= => har heq; have [Hx [Hy Hz]]:=(area_p _ _ _ har).
have hxnp:x<>p.
  move=> hxep; rewrite hxep in har.
  have Hbad: p ^ 2 + 4 * y * z > p by mcnia. rewrite {1} har in Hbad.
  by move: Hbad; rewrite ltn_neqAle=> /andP [/eqP Hbad _]; apply: Hbad.
rewrite -heq expnSr mulnC (mulnC 4 x) -mulnA in har.
have [_ divp] := primeP p_prime.
have [/eqP hyes |/eqP hno] : (x == 1) \/ (x == p).
  apply/orP; apply: divp. by rewrite /dvdn har /expnSr -modnDm !modnMr addn0 mod0n.
by split; first by []; rewrite -heq. by exfalso.
Qed.

Lemma bound_Sp: forall (t:N3), p = area t ->  t.1.1<p /\ t.1.2<p /\ t.2<p.
Proof.
move => [[x y] z] ; rewrite /area /= => Harea.
have [/= Hxn0 [Hyn0 Hzn0]] := area_p _ _ _ Harea.
split; [|split].
    case (x < p) eqn: Hx => //=.
    rewrite -> Harea in Hx. assert(Hx' : z < z ^ 2 + 4 * y * z) by mcnia.
    by rewrite -Hx; mcnia.
    case (y < p) eqn: Hy; first by [].
      rewrite -> Harea in Hy. assert(Hy' : y < x ^ 2 + 4 * y * z) by mcnia.
      by rewrite -Hy; mcnia.
    case (z < p) eqn: Hz; first by [].
      rewrite -> Harea in Hz. assert(Hz' : z < x ^ 2 + 4 * y * z) by mcnia.
      by rewrite -Hz; mcnia.
Qed.

(** Study of the zig involution **)

Lemma zig_involution: involutionN3 S zig.
Proof.
rewrite /involution_on; split.
 + move => t; rewrite !inE /zig /= => htS; destruct_boolhyp htS; move => hp hz hy.
   by repeat (apply /andP; split => //=); rewrite (eqP hp) /area /=; mcnia.
 + by move => [[a b] c] hxs; rewrite /zig.
Qed.

Lemma zig_solution (t:N3):
  (t \in fixed_fset [choiceType of N3] S zig)->(exists a b: nat, p=a^2+b^2).
Proof.
rewrite !inE /area /zig => htfix; destruct_boolhyp htfix; move => ht hp hz hy.
have heqt:t.2=t.1.2 by move/eqP: ht =>  {1}-> .
rewrite -heqt in ht; exists t.1.1; exists (2*(t.2)).
rewrite (eqP hp). mcnia.
Qed.

(** Study of the zag involution **)

Lemma zag_involution: involutionN3 S zag.
Proof.
rewrite /involution_on; split.
 + move => t; rewrite !inE => /andP [hIp /eqP har]; apply/andP.
   have hzagar: p = area (zag t) by rewrite har /area /zag; zag_solve.
   split; last by rewrite hzagar. move/bound_Sp: hzagar => [h1 [h2 h3]] /=.
   apply/andP; split; first by apply/andP; split; apply/in_Ipfset. by apply/in_Ipfset.
 + move => [[ /=x y] /= z]; rewrite !inE => htS; destruct_boolhyp htS; move => /eqP hp hz hy.
   have [hx0 [hy0 hz0]] := area_p x y z hp. by rewrite /zag; zag_solve.
Qed.

Lemma zag_fixed_point (k:nat): (p = k*4+1) -> (fixed_fsetN3 S zag)=[fset (1,1,k)].
Proof.
move => h_pmod4; apply/eqP; rewrite eqEfsubset; apply/andP; split.
 + apply/fsubsetP => t. rewrite !inE. move: t=>[[x y] z].
   move => /andP [/andP [_ /eqP har] /eqP hzagt]. apply /eqP.
   - have hx1:(x = 1). move: hzagt. rewrite /zag. move => Heq /=.
     by apply (area_p_xy _ _ _ har); generalize Heq; zag_solve.
   - have hy1:(y = 1). move: hzagt. rewrite /zag. move => Heq /=.
     by apply (area_p_xy _ _ _ har); generalize Heq; zag_solve.
   - rewrite /area in har. by zag_solve.
 + apply/fsubsetP => x; rewrite !inE => /eqP -> /=.
   have harea : p=area (1,1,k) by rewrite/area h_pmod4 /=; ring.
   have [/= hbx [_ hbz]] := bound_Sp (1,1,k) harea.
   repeat (apply/andP; split); try apply/in_Ipfset; zag_solve => //=.
Qed.


(** The final proof **)
(* We give this proof with Zagier's 'one-sentence' as comment *)

Theorem Fermat_Zagier : (modn p 4 = 1) -> (exists a b :nat, p=a^2 + b^2).
Proof.
move /modulo_ex => [k hk].
(* 'The involution on the finite set [S] defined by [zag]' *)
have h_zag_invol:=zag_involution.
(* 'has exactly one fixed point,' *)
have h_zag_fix_card:(#|`(fixed_fsetN3 S zag)|) = 1.
   + by rewrite (zag_fixed_point k); first by apply: cardfs1; exact hk.
(* 'so |S| is odd,' *)
have h_S_odd: odd(#|`S|).
   by rewrite -(InvolutionN3_lemma zag S h_zag_invol) h_zag_fix_card.
(* 'and the involution defined by [zig].' *)
have h_zig_invol:= zig_involution.
(* 'also has a fixed point.' *)
have [t htzigfix]: exists t:N3, t \in (fixed_fsetN3 S zig).
  by apply odd_existence; rewrite (InvolutionN3_lemma zig S h_zig_invol).
by apply (zig_solution t).
Qed.

End Zagier_proof.
Check Fermat_Zagier.

(**                                                                        **
 *                End of the proof of Fermat's Theorem                      *
 **                                                                        **)
