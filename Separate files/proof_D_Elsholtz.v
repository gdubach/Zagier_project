(*  File 5/5 of the proofs of Fermat's Two Squares Theorem                    *)
(*                          by G. Dubach and F. Muehlboeck, IST Austria, 2021 *)
(*                                                                            *)
(*  This proof is from:                                                       *)
(* Elsholtz*)
(*                                                                            *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import finmap.
Require Import lemmata.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Elsholtz_Proof.
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
Definition area (t:N3) :nat := 3*(t.1.1)^2+4*(t.1.2)*(t.2).
Definition S:{fset N3} := [fset t:N3 | t \in Ipf3 & (p == area(t))].
Definition zig (t : N3) :N3 := (t.1.1, t.2, t.1.2).
Definition elsholtz (t:N3) :N3 := match t with 
(x,y,z) => if 2 * y <= x        then ( x - 2 * y , 3*x + z - 3*y , y )
 else if 3 * y <= 3 * x + z     then ( 2 * y - x , y , 3 * x + z - 3 * y )
 else if 4 * y <= 5 * x + 2 * z then ( 5 * x + 2 * z - 4 * y , 6 * x + 3 * z - 4 * y , 3 * y - (3 * x + z) )
 else if 4 * y <= 6 * x + 3 * z then ( 4 * y - 5 * x - 2 * z , 3 * y - 3 * x - z , 6 * x + 3 * z - 4 * y )
 else if 4 * y <= 7 * x + 4 * z then ( 7 * x + 4 * z - 4 * y , 6 * x + 4 * z - 3 * y , 4 * y - 6 * x - 3 * z )
 else if 3 * y <= 6 * x + 4 * z then ( 4 * y - 7 * x - 4 * z , 4 * y - 6 * x - 3 * z , 6 * x + 4 * z - 3 * y )
 else if 2 * y <= 5 * x + 4 * z then ( 5 * x + 4 * z - 2 * y , 3 * x + 3 * z - y , 3 * y - 6 * x - 4 * z )
 else if     y <= 3 * x + 3 * z then ( 2 * y - 5 * x - 4 * z , 3 * y - 6 * x - 4 * z , 3 * x + 3 * z - y )
                                else ( x + 2 * z , z , y - (3 * x + 3 * z) ) end.

(* Work on stability *)

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

Lemma area_p (x y z : nat) : p = area (x,y,z) -> x > 0 /\ y > 0 /\ z > 0.
Proof.
Admitted.

Lemma area_p_xy (x y z : nat) : p = area (x,y,z) -> x = y -> x = 1 /\ y = 1.
Proof.
Admitted.

Lemma bound_Sp: forall (x y z : nat), p = area (x,y,z) ->  x < p /\ y < p /\ z <p.
Proof.
move => x y z ; rewrite /area /= => Harea.
have [/= Hxn0 [Hyn0 Hzn0]] := area_p Harea.
split; [|split]; by_contradiction hcontra => //=;
  rewrite Harea in hcontra; rewrite -hcontra; mcnia.
Qed.

Lemma elsholtz_involution: involutionN3 S elsholtz.
Proof.
rewrite/involution_on; split; move => [[x y] z]. admit. 
 - rewrite !inE /elsholtz => htS; destruct_boolhyp htS => hx hy hz /eqP hp.
   have harea_p := area_p hp.
   zag_solve.
zag_solve.
 - rewrite !inE /area /elsholtz /Ipfset /= => hin.
  destruct_boolhyp hin => hx hy hz /eqP hp.
   have harea_p := area_p hp.
   have hboundp := bound_Sp hp.
   + case_eq (2 * y <= x). move=> h1.
repeat (apply/andP; split). mcnia. admit. mcnia. mcnia.
   + case_eq (3 * y <= 3 * x + z). zag_solve.
   + case_eq (4 * y <= 5 * x + 2 * z). zag_solve.
   + case_eq (4 * y <= 6 * x + 3 * z).
   + case_eq (4 * y <= 7 * x + 4 * z).
   + case_eq (3 * y <= 6 * x + 4 * z).
   + case_eq (2 * y <= 5 * x + 4 * z).

zag_solve.
   destruct_boolhyp hin => hx hy hz /eqP hp.
   have harea_p := area_p hp.
   destruct harea_p as [hx' [hy' hz']].
   case_eq (2 * y <= x).
   zag_solve.
   case_eq (2 * y <= 2 * x + z).
   zag_solve.
   case_eq (2 * y <= 3 * x + 2 * z).
   intros.
   repeat (apply /andP; split).
   zag_solve.
   zag_solve.
   zag_solve.
   rewrite /=.
   have hhhh : 2 * x + 2 * z >= y by mcnia.
   mcnia.
 - rewrite !inE /jack => htS; destruct_boolhyp htS => hx hy hz /eqP hp.
   have harea_p := area_p hp.
   zag_solve.
Qed.

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
     mcnia. mcnia. mcnia. mcnia.
   + case_eq (2 * y <= 4*x + 4 * z). zag_solve.
   + zag_solve.
 - rewrite !inE /jack => htS; destruct_boolhyp htS => hx hy hz /eqP hp.
   have harea_p := area_p hp.
   zag_solve.
Qed.

Lemma foo1 (x y z : nat) : 2 * y <= x -> area(x,y,z)=area( elsholtz(x,y,z) ).
Proof.
move=> hle; rewrite/area/elsholtz.
zag_solve.
Qed.

Lemma foo2 (x y z : nat) : 2 * y >= x -> 3 * y <= 3 * x + z 
-> area(x,y,z)=area( elsholtz(x,y,z) ).
Proof.
move=> hge hle; rewrite/area/elsholtz.
zag_solve.
Qed.

Lemma foo3 (x y z : nat) : (2 * y <= x)=false -> (3 * y <= 3 * x + z)=false -> 4 * y <= 5 * x + 2 * z
-> area(x,y,z)=area( elsholtz(x,y,z) ).
Proof.
move=> hge1 hge2 hle; rewrite/area/elsholtz. zag_unfold. mcsolve.
Qed.

Lemma foo9 (x y z : nat) : (y <= 3 * x + 3 * z)=false
-> area(x,y,z)=area( x + 2 * z , z , y - (3 * x + 3 * z) ).
Proof.
move=> hge; rewrite/area/elsholtz.
zag_solve.
Qed.

Lemma foo4 (x y z : nat) : 4 * y >= 5 * x + 2 * z -> 4 * y <= 6 * x + 3 * z
-> area(x,y,z)=area( elsholtz(x,y,z) ).
Proof.
move=> hge hle; rewrite/area/elsholtz.
zag_solve.
Qed.

Lemma foo5 (x y z : nat) : 3 * y >= 3 * x + z -> 4 * y <= 5 * x + 2 * z
-> area(x,y,z)=area( elsholtz(x,y,z) ).
Proof.
move=> hge hle; rewrite/area/elsholtz.
zag_solve.
Qed.




Lemma elsholtz_involution: involutionN3 S elsholtz.
Proof.
rewrite/involution_on; split; move => [[x y] z].
 - rewrite !inE /area /elsholtz /Ipfset /= => hin.
zag_solve.
   destruct_boolhyp hin => hx hy hz /eqP hp.
   have harea_p := area_p hp.
   destruct harea_p as [hx' [hy' hz']].
   case_eq (2 * y <= x).
   zag_solve.
   case_eq (2 * y <= 2 * x + z).
   zag_solve.
   case_eq (2 * y <= 3 * x + 2 * z).
   intros.
   repeat (apply /andP; split).
   zag_solve.
   zag_solve.
   zag_solve.
   rewrite /=.
   have hhhh : 2 * x + 2 * z >= y by mcnia.
   mcnia.
 - rewrite !inE /jack => htS; destruct_boolhyp htS => hx hy hz /eqP hp.
   have harea_p := area_p hp.
   zag_solve.
Qed.



Variable p_gt2 : p > 2.

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
   destruct harea_p as [hx' [hy' hz']].
   case_eq (2 * y <= x).
   zag_solve.
   case_eq (2 * y <= 2 * x + z).
   zag_solve.
   case_eq (2 * y <= 3 * x + 2 * z).
   intros.
   repeat (apply /andP; split).
   zag_solve.
   zag_solve.
   zag_solve.
   rewrite /=.
   have hhhh : 2 * x + 2 * z >= y by mcnia.
   mcnia.
 - rewrite !inE /jack => htS; destruct_boolhyp htS => hx hy hz /eqP hp.
   have harea_p := area_p hp.
   zag_solve.
Qed.

Lemma zag_fixed_point (k:nat): (p = k*8+3) -> (fixed_fsetN3 S jack)=[fset (1,1,4 * k + 1)].
Proof.
move => h_pmod4; apply/eqP; rewrite eqEfsubset; apply/andP; split.
 - apply/fsubsetP => t; move: t=>[[x y] z] /=.
   rewrite !inE /jack /=.
   move => hp; destruct_boolhyp hp => /= hx hy hz /eqP hp hxe.
   have [hx0 [hy0 hz0]] := area_p hp.
   have hxy := (area_p_xy hp); hyp_progress hxy; generalize dependent hxe; zag_solve.
   rewrite /area in hp; simpl in *.
   zag_solve.
 - apply/fsubsetP => x; rewrite !inE => /eqP -> /=.
   have harea : p=area (1,1,4 * k + 1) by rewrite/area h_pmod4 /=; ring.
   have [/= hbx [_ hbz]] := bound_Sp harea.
   repeat (apply/andP; split); try apply/in_Ipfset; zag_solve => //=.
Qed.

(*                                                                            *)
(*  Zagier's proof                                                            *)
(*  (Zagier's 'one-sentence' is given as comments)                            *)
(*                                                                            *)

Theorem Fermat_Elsholtz : p %% 4 = 1 -> exists a b :nat, p=a^2 + b^2.
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

End Elsholtz.
Check Fermat_Elsholtz.
