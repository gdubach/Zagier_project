(*  File 3/3 of the proofs of Fermat's Two Squares Theorem                    *)
(*                          by G. Dubach and F. Muehlboeck, IST Austria, 2021 *)
(*                                                                            *)
(*  This proof is from:                                                       *)
(*    A. David Christopher                                                    *)
(*    A partition-theoretic proof of Fermat’s Two Squares Theorem             *)
(*    Discrete Mathematics 339 (2016), no. 4, 1410-1411.                      *)
(*                                                                            *)

From mathcomp Require Import all_ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import choice path finset finfun fintype bigop finmap.
Require Import lemmata.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Lemma modulo_ex: p %% 4 = 1 -> exists k, p=k*4+1.
Proof.
by move => h_pmod4; exists (p%/4); rewrite{1} (divn_eq p 4) h_pmod4.
Qed.

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

