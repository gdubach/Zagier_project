(*  Additional file of Zagier Project                                         *)
(*                          by G. Dubach and F. Muehlboeck, IST Austria, 2021 *)
(*                                                                            *)
(*  This proof is from:                                                       *)
(* C. Elsholtz, and others ? *)
(*                                                                            *)

From mathcomp Require Import all_ssreflect finmap.
Require Import lemmata.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Jackson_Proof.
Open Scope nat_scope.

Variable p:nat.
Variable p_prime : prime p.
Variable p_gt2 : p > 2.

Definition N3 : Type := nat * nat * nat.
Definition involutionN3:= (@involution_on [choiceType of N3]).
Definition fixed_fsetN3:=(@fixed_fset [choiceType of N3]).
Definition involutionN3_lemma:=(@involution_lemma [choiceType of N3]).
Definition Ipfset:{fset nat} := [fsetval n in 'I_p].
Definition Ipf3:{fset N3} := (Ipfset`*`Ipfset`*`Ipfset).
Definition area (t:N3) :nat := (t.1.1)^2 + 2 * (t.1.2) * (t.2).
Definition S:{fset N3} := [fset t:N3 | t \in Ipf3 & (p == area(t))].
Definition zig (t : N3) :N3 := (t.1.1, t.2, t.1.2).
Definition jack (t:N3) :N3 := match t with (x,y,z) =>
      if 2 * y <= x             then (x - 2 * y, z + x + ( x - 2 * y), y)
 else if 2 * y <= 2 * x + z     then (2 * y - x, y, (2 * x + z) - 2 * y)
 else if 2 * y <= 3 * x + 2 * z then ((3 * x + 2 * z) - 2 * y, (2 * x + 2*z) - y, 2 * y - (2 * x + z))
 else if 2 * y <= 4 * x + 4 * z then (2 * y - (3 * x + 2 * z), 2 * y - (2 * x + z), 2 * x + 2 * z - y)
                                else (x + 2 * z, z, y - (2 * x + 2 * z)) end.

(*  Basic properties                                                          *)

Lemma modulo_ex: ((modn p 8) = 3) -> (exists k, p=k*8+3).
Proof.
by move => h_pmod8; exists (p%/8); rewrite{1} (divn_eq p 8) h_pmod8.
Qed.

Lemma square_eq : forall n : nat, n * n == n -> (n == 1) || (n == 0).
Proof.
move => n /eqP hnn.
by have [->|->]:(n = 1) \/ (n = 0) by mcnia.
Qed.

Lemma _2_div_p : (2 %|p) -> False.
Proof.
move => h2p.
have p_2 : 2 == p.
by rewrite -(dvdn_prime2 _ p_prime).
have hpgt2 := p_gt2.
by rewrite (eqP p_2) ltnn in hpgt2.
Qed.

Lemma _4_div_p : (4 %|p) -> False.
Proof.
move => h4p.
have /_2_div_p h2p: 2%|p by apply (@dvdn_trans 4 2 p).
by [].
Qed.

Lemma area_x (x y z : nat) : p=area (x,y,z) -> ~(x = 0).
Proof.
rewrite /area => har h0; move: h0 har => -> /=.
rewrite (expnD 0 1 1) (expn1 0) muln0 add0n.
rewrite -mulnA => har; apply: _2_div_p; by rewrite har !dvdn_mulr.
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
  have Hbad: p ^ 2 + 2 * y * z > p by mcnia.
  rewrite {1} har in Hbad.
  by move: Hbad; rewrite ltn_neqAle=> /andP [/eqP Hbad _]; apply: Hbad.
rewrite -heq expnSr mulnC (mulnC 2 x) -mulnA in har.
have [_ divp] := primeP p_prime.
have [/eqP hyes |/eqP hno] : (x == 1) \/ (x == p).
- apply/orP; apply: divp.
  by rewrite /dvdn har /expnSr -modnDm !modnMr addn0 mod0n.
- by split; first by []; rewrite -heq.
by exfalso.
Qed.

Lemma bound_Sp: forall (x y z : nat), p = area (x,y,z) ->  x < p /\ y < p /\ z <p.
Proof.
move => x y z ; rewrite /area /= => Harea.
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
  (t \in fixed_fset S zig)->(exists a b: nat, p=a^2+ 2 * b^2).
Proof.
rewrite !inE /area /zig => htfix; destruct_boolhyp htfix => hx hy hz hp _ ht _.
rewrite /= in ht.
exists t.1.1; exists ((t.2)).
mcnia.
Qed.

(* Study of the jack involution                                                *)

Lemma jack_involution: involutionN3 S jack.
Proof.
rewrite /involution_on; split; move => [[x y] z].
 - rewrite !inE /area /jack /Ipfset /= /area /jack => hin.
   destruct_boolhyp hin => hx hy hz /eqP hp.
   have harea_p := area_p hp.
   have hboundp := bound_Sp hp.
(* We distinguish the cases. Number 3 takes a lot of time. *)
   + case_eq (2 * y <= x). zag_solve.
   + case_eq (2 * y <= 2 * x + z). zag_solve.
   + case_eq (2 * y <= 3 * x + 2 * z). simpl.
     move=> h3 h2 h1; repeat (apply/andP; split).
     admit. admit. admit. mcnia.
   + case_eq (2 * y <= 4*x + 4 * z). zag_solve.
   + zag_solve.
 - rewrite !inE /jack => htS; destruct_boolhyp htS => hx hy hz /eqP hp.
   have harea_p := area_p hp.
   zag_solve.
Admitted.

Lemma jack_fixed_point (k:nat): (p = k*8+3) -> (fixed_fsetN3 S jack)=[fset (1,1,4 * k + 1)].
Proof.
move => h_pmod8; apply/eqP; rewrite eqEfsubset; apply/andP; split.
 - apply/fsubsetP => t; move: t=>[[x y] z] /=.
   rewrite !inE /jack /=. 
   move => hp; destruct_boolhyp hp => /= hx hy hz /eqP hp hxe.
  have harea_p := area_p hp.
  have hareaxy_p := area_p_xy hp.
  hyp_progress hareaxy_p. generalize dependent hxe. zag_solve.
zag_solve.
case_eq (2 * y <= x). move => hypy. simpl. move=> h1 h2 h3. exfalso. zag_solve.
   have [hx0 [hy0 hz0]] := area_p hp.
   have hxy := (area_p_xy hp); hyp_progress hxy; generalize dependent hxe; zag_solve.
   rewrite /area in hp; simpl in *.
   zag_solve. zag_solve. admit. admit. admit.
 - apply/fsubsetP => x; rewrite !inE => /eqP -> /=.
   have harea : p=area (1,1,4 * k + 1) by rewrite/area h_pmod8 /=; ring.
   have [/= hbx [_ hbz]] := bound_Sp harea.
   repeat (apply/andP; split); try apply/in_Ipfset; zag_solve => //=.
Admitted.

(*                                                                            *)
(*  Jackson's   proof                                                         *)
(*  (Zagier's one-sentence written as comment                                 *)
(*                                                                            *)

Theorem Fermat_Jackson : p %% 8 = 3 -> exists a b :nat, p = a^2 + 2 * b^2.
Proof.
move /modulo_ex => [k hk].
(* 'The involution on the finite set [S] defined by [jack]'                    *)
have h_jack_invol:=jack_involution.
(* 'has exactly one fixed point,'                                             *)
have h_jack_fix_card:(#|`(fixed_fsetN3 S jack)|) = 1.
   - by rewrite (jack_fixed_point hk); first by apply: cardfs1.
(* 'so |S| is odd,'                                                           *)
have h_S_odd: odd(#|`S|).
   by rewrite -(involutionN3_lemma h_jack_invol) h_jack_fix_card.
(* 'and the involution defined by [zig].'                                     *)
have h_zig_invol:= zig_involution.
(* 'also has a fixed point.'                                                  *)
have [t htzigfix]: exists t:N3, t \in (fixed_fsetN3 S zig).
  by apply odd_existence; rewrite (involutionN3_lemma h_zig_invol).
by apply (zig_solution htzigfix).
Qed.

End Jackson_Proof.
Check Fermat_Jackson.
