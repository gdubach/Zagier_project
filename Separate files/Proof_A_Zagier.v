(*  File 2/3 of the proofs of Fermat's Two Squares Theorem                    *)
(*                          by G. Dubach and F. Muehlboeck, IST Austria, 2021 *)
(*                                                                            *)
(*  This proof is from:                                                       *)
(*  D. Zagier, A One-Sentence Proof That Every Prime p $\equiv$ 1 (mod 4)     *)
(*  is a Sum of Two Squares,                                                  *)
(*                The American Mathematical Monthly 97 (1990), no.2, 144-144. *)
(*                                                                            *)

From mathcomp Require Import all_ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import choice path finset finfun fintype bigop finmap.
From mathcomp Require Import ssralg order.
Require Import lemmata.
Set Implicit Argument.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Zagier_Proof.
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
Definition S:{fset N3} := [fset t:N3 | t \in Ipf3 & (p == area(t))].
Definition zig (t : N3) :N3 := (t.1.1, t.2, t.1.2).
Definition zag (t:N3) :N3 := match t with (x,y,z) =>
 if y >= (x+z) then (x+2*z,z,y-(x+z))
    else if (2*y) >= x then (2*y-x,y,z+x-y)
         else (x-2*y,z+x-y,y) end.


(*  Basic properties                                                          *)

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

(* Study of the zig involution                                                *)

Lemma zig_involution: involutionN3 S zig.
Proof.
rewrite /involution_on; split.
 - move => t; rewrite !inE /zig /= => htS; destruct_boolhyp htS; move => hp hz hy.
   by repeat (apply /andP; split => //=); rewrite (eqP hp) /area /=; mcnia.
 - by move => [[a b] c] hxs; rewrite /zig.
Qed.

Lemma zig_solution (t:N3):
  (t \in fixed_fset [choiceType of N3] S zig)->(exists a b: nat, p=a^2+b^2).
Proof.
rewrite !inE /area /zig => htfix; destruct_boolhyp htfix; move => ht hp hz hy.
have heqt:t.2=t.1.2 by move/eqP: ht =>  {1}-> .
rewrite -heqt in ht; exists t.1.1; exists (2*(t.2)).
rewrite (eqP hp). mcnia.
Qed.

(* Study of the zag involution                                                *)

Lemma zag_involution: involutionN3 S zag.
Proof.
rewrite /involution_on; split.
 - move => t; rewrite !inE => /andP [hIp /eqP har]; apply/andP.
   have hzagar: p = area (zag t) by rewrite har /area /zag; zag_solve.
   split; last by rewrite hzagar. move/bound_Sp: hzagar => [h1 [h2 h3]] /=.
   apply/andP; split; first by apply/andP; split; apply/in_Ipfset. by apply/in_Ipfset.
 - move => [[ /=x y] /= z]; rewrite !inE => htS; destruct_boolhyp htS; move => /eqP hp hz hy.
   have [hx0 [hy0 hz0]] := area_p x y z hp. by rewrite /zag; zag_solve.
Qed.

Lemma zag_fixed_point (k:nat): (p = k*4+1) -> (fixed_fsetN3 S zag)=[fset (1,1,k)].
Proof.
move => h_pmod4; apply/eqP; rewrite eqEfsubset; apply/andP; split.
 - apply/fsubsetP => t. rewrite !inE. move: t=>[[x y] z].
   move => /andP [/andP [_ /eqP har] /eqP hzagt]. apply /eqP.
   + have hx1:(x = 1). move: hzagt. rewrite /zag. move => Heq /=.
     by apply (area_p_xy _ _ _ har); generalize Heq; zag_solve.
   + have hy1:(y = 1). move: hzagt. rewrite /zag. move => Heq /=.
     by apply (area_p_xy _ _ _ har); generalize Heq; zag_solve.
   + rewrite /area in har. by zag_solve.
 - apply/fsubsetP => x; rewrite !inE => /eqP -> /=.
   have harea : p=area (1,1,k) by rewrite/area h_pmod4 /=; ring.
   have [/= hbx [_ hbz]] := bound_Sp (1,1,k) harea.
   repeat (apply/andP; split); try apply/in_Ipfset; zag_solve => //=.
Qed.

(*                                                                            *)
(*  Zagier's proof                                                            *)
(*  (Zagier's 'one-sentence' is given as comments)                            *)
(*                                                                            *)

Theorem Fermat_Zagier : (modn p 4 = 1) -> (exists a b :nat, p=a^2 + b^2).
Proof.
move /modulo_ex => [k hk].
(* 'The involution on the finite set [S] defined by [zag]'                    *)
have h_zag_invol:=zag_involution.
(* 'has exactly one fixed point,'                                             *)
have h_zag_fix_card:(#|`(fixed_fsetN3 S zag)|) = 1.
   - by rewrite (zag_fixed_point k); first by apply: cardfs1; exact hk.
(* 'so |S| is odd,'                                                           *)
have h_S_odd: odd(#|`S|).
   by rewrite -(InvolutionN3_lemma zag S h_zag_invol) h_zag_fix_card.
(* 'and the involution defined by [zig].'                                     *)
have h_zig_invol:= zig_involution.
(* 'also has a fixed point.'                                                  *)
have [t htzigfix]: exists t:N3, t \in (fixed_fsetN3 S zig).
  by apply odd_existence; rewrite (InvolutionN3_lemma zig S h_zig_invol).
by apply (zig_solution t).
Qed.

End Zagier_Proof.
Check Fermat_Zagier.
