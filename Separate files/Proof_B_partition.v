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
Definition InvolutionN4_lemma:=(@Involution_lemma [choiceType of N4]).

(* Y_area is the area of a Young diagram                                      *)
Definition Y_area (yd : N4) : nat := yd.1.1*yd.1.2+yd.2.1*yd.2.2.

Definition P2p :=[fset yd:N4 | (yd \in Ip4) && ((Y_area yd ==p)&&(yd.1.1>yd.2.1))].
  Definition P2p_l :=[fset yd:N4 | (yd \in P2p) && (yd.1.2<yd.2.2)].
  Definition P2p_e :=[fset yd:N4 | (yd \in P2p) && (yd.1.2==yd.2.2)].
  Definition P2p_g :=[fset yd:N4 | (yd \in P2p) && (yd.1.2>yd.2.2)].

(* Basic properties                                                           *)

Lemma in_Ip (n : nat) : (n \in Ip) <-> (n<p).
Proof.
split; first by rewrite /Ip => /imfsetP /= [x _ ->].
by move => hnp; apply/imfsetP; exists (Sub n hnp).
Qed.

Lemma modulo_ex: ((modn p 4) = 1) -> (exists k, p=k*4+1).
Proof. by move => h_pmod4; exists (p%/4); rewrite{1} (divn_eq p 4) h_pmod4. Qed.

Lemma Ip4_not_p_factors (a f : nat): a \in Ip -> f \in Ip -> ~ (a * f == p).
Proof.
  move => ha hf. destruct (a * f == p) eqn: hassume; [|done].
    have hda : a %| p. unfold dvdn. rewrite -(eqnP hassume). by rewrite modnMr.
    have hdf : f %| p. unfold dvdn. rewrite -(eqnP hassume). by rewrite modnMl.
    have [hp hdiv] := (primeP p_prime). apply in_Ip in ha,hf.
      apply hdiv in hda. apply hdiv in hdf. destruct_boolhyp hda; destruct_boolhyp hdf.
        rewrite (eqnP hda) (eqnP hdf) mul1n in hassume. by rewrite -(eqnP hassume) in hp.
        by rewrite (eqnP hdf) ltnn in hf.
        by rewrite (eqnP hda) ltnn in ha.
        by rewrite (eqnP hda) ltnn in ha.
Qed.

Lemma area_gt0_all : forall yd : N4, (yd \in Ip4) -> Y_area yd == p 
-> (yd.1.1 > 0)/\(yd.1.2>0)/\(yd.2.1>0)/\(yd.2.2>0).
Proof.
rewrite /Y_area. move => [[a1 f1] [a2 f2]] hin11 harea. rewrite !inE in hin11.
destruct_boolhyp hin11 => /= hina1 hinf1 hina2 hinf2; simpl in *.
split. destruct a1; [|done]. exfalso. rewrite mul0n add0n in harea.
       by apply (@Ip4_not_p_factors a2 f2 hina2 hinf2).
split. destruct f1; [|done]. exfalso. rewrite muln0 add0n in harea.
       by apply (@Ip4_not_p_factors a2 f2 hina2 hinf2).
split. destruct a2; [|done]. exfalso. rewrite mul0n addn0 in harea.
       by apply (@Ip4_not_p_factors a1 f1 hina1 hinf1).
       destruct f2; [|done]. exfalso. rewrite muln0 addn0 in harea.
       by apply (@Ip4_not_p_factors a1 f1 hina1 hinf1).
Qed.

Lemma P2p_in_Ip4 (yd:N4): (yd \in P2p)-> (yd \in Ip4).
Proof. rewrite inE; by rewrite inE => /andP [hinI4 _]. Qed.

(* Study of P2p via conjugation                                               *)

Definition conjugate (a : N4) : N4:= ((a.1.2 + a.2.2,a.2.1),(a.1.2,a.1.1-a.2.1)).

Lemma conjugate_involution : involutionN4 P2p conjugate.
Proof. 
split.
 - move => yd hin11. have hinI4 := (@P2p_in_Ip4 yd hin11).
   rewrite !inE in hin11. destruct_boolhyp hin11 => hina1 hinf1 hina2 hinf2 harea hleq. 
   have [ha1 [hf1 [ha2 hf2]]] := (@area_gt0_all yd hinI4 harea).
   rewrite /conjugate. rewrite !inE.
   rewrite /Y_area in harea; rewrite /Y_area.
   repeat (apply /andP; split); try apply in_Ip; mcnia.
 - move => yd hin11; rewrite !inE in hin11. 
   destruct_boolhyp hin11 => hina1 hinf1 hina2 hinf2 _. 
   rewrite /conjugate; destruct yd as [[a1 f1] [a2 f2]]; simpl; simpl in *.
   zag_solve.
Qed.

Lemma conjugate_fixed : (modn p 4  = 1) -> #|`fixed_fsetN4 P2p conjugate| = 1.
Proof.
move /modulo_ex => [k hk].
have h_singleton : fixed_fsetN4 P2p conjugate = [fset ((2*k+1,1),(1,2*k))].
 - apply/eqP; rewrite eqEfsubset; apply/andP; split.
   + apply/fsubsetP => yd. rewrite !inE /conjugate. move: yd=>[[a1 f1] [a2 f2]] /= ha.
       destruct_boolhyp ha; move => /= ha1 hf1 ha2 hf2 harea hlt heq hf1a2 ha2f1 hf2a1a2.
       mcsimpl; subst; rewrite /Y_area /= in harea.
       apply in_Ip in ha1, ha2, hf1, hf2.
       have harea' : a2 * (a2 + f2 + f2) == p by mcnia.
       have hdvdn : a2 %| p.
       - apply /dvdnP; exists (a2 + f2 + f2); rewrite mulnC; symmetry; by apply /eqnP.
       have ha2_1: a2 = 1.
       - have p_prime' := p_prime; apply (elimT primeP) in p_prime'.
         destruct p_prime' as [_ hdiv]; apply hdiv in hdvdn; destruct_boolhyp hdvdn; mcnia.
       repeat rewrite xpair_eqE. repeat (apply /andP; split); try mcnia.
   + apply/fsubsetP => yd. rewrite !inE. move: yd=>[[a1 f1] [a2 f2]].
     move /eqP => [ha1 hf1 ha2 hf2]. rewrite ha1 hf1 ha2 hf2.
     have kgt0 : k > 0. destruct (k > 0) eqn: hkgt0; [by []|]. have hk0: (k = 0). by mcnia. subst.
        have p_prime' := p_prime. apply (elimT primeP) in p_prime'. by destruct p_prime' as [lt1_1 _].
     repeat (apply /andP; split); try (simpl; try rewrite /Y_area; try apply in_Ip; mcnia; fail).
rewrite h_singleton; by rewrite cardfs1.
Qed.

Lemma P2p_odd :  (modn p 4  = 1) -> odd(#|`P2p|).
Proof.
rewrite -(@InvolutionN4_lemma conjugate P2p conjugate_involution). move => hp4.
by rewrite conjugate_fixed.
Qed.

(* Study of P2p_l via double transposition                                    *)

Definition transpose_l (a : N4) : N4:= ((a.2.2,a.2.1),(a.1.2,a.1.1)).

Lemma transpose_l_involution : involutionN4 P2p_l transpose_l.
Proof.
split.
 - move => yd hin11; rewrite !inE in hin11.
   destruct_boolhyp hin11 => ha1 hf1 ha2 hf2 /eqP harea hlta hltf. 
   rewrite /transpose_l; rewrite !inE. repeat (apply /andP; split).
   by []. by []. by []. by []. rewrite -harea /Y_area; simpl. mcnia.
   by simpl. by simpl.
 - move => yd hin11; rewrite !inE in hin11.
   destruct_boolhyp hin11 => h12l22 /eqP harea hin21l11 hin21 hin22 hin12.
   rewrite /transpose_l; destruct yd as [[a1 f1] [a2 f2]]. by [].
Qed.

Lemma transpose_l_fixed : #|`fixed_fsetN4 P2p_l transpose_l| = 0.
Proof. 
  have fset_eq_0 : fixed_fsetN4 P2p_l transpose_l = fset0; [|by rewrite fset_eq_0].
  rewrite /fixed_fsetN4 /fixed_fset. apply (elimT eqP). rewrite -fsubset0.
  by_contradiction hsubset.
    apply (introT negPf) in hsubset. apply (elimT (fsubsetPn _ _)) in hsubset.
      destruct hsubset as [[[a1 f1] [a2 f2]] hin _]. rewrite !inE in hin.
      destruct_boolhyp hin => /= ha1 hf1 ha2 hf2 harea ha2a1 hf1f2 ha1f2 hf1a2 ha2f1 hf2a1.
      (*rewrite /transpose_l /= in htpl. repeat rewrite xpair_eqE in htpl.*)
      (*destruct_boolhyp htpl. move => htpl' _ _. apply (elimT eqnP) in htpl,htpl'.*)
      mcsimpl; subst.
      rewrite /Y_area /= in harea.
      have p_prime' := p_prime. apply (elimT primeP) in p_prime'.
      destruct p_prime' as [hp1 hdvdnp]. have harea' : 2 * (a2 * f2) == p. by mcnia.
      have hdvdn : 2 %| p. apply /dvdnP. exists (a2 * f2). mcnia.
      apply hdvdnp in hdvdn. simpl in hdvdn.
      have hf1gt0 : a2 > 0. by mcnia.
      have hf2gt0 : f2 > 0. by mcnia.
      have hgt : 2 * a2 * f2 > p. by mcnia. rewrite -mulnA (eqnP harea') in hgt.
      by rewrite ltnn in hgt.
Qed.

Theorem P2p_l_even : ~~odd(#|`P2p_l|).
Proof.
rewrite -(@InvolutionN4_lemma transpose_l P2p_l transpose_l_involution).
by rewrite transpose_l_fixed.
Qed.

(* Study of P2p_e via enumeration                                             *)

Lemma mod4_halfeven : (modn p 4  = 1) -> (divn (p - 1) 2) %% 2 == 0.
Proof.
  move => hpmod. apply (elimT primeP) in p_prime. destruct p_prime as [hp1 hdvdn].
  have hp: (p - 1).+1 = p by mcnia.
  have hp1mod : (p-1) %% 4 = 0. rewrite subn1 modn_pred; [|by []| auto;fail].
    by rewrite hpmod /= /dvdn hpmod /=.
  by rewrite modn_divl /muln /= hp1mod div0n.
Qed.

Definition P2p_e_mapfun : nat -> N4 := fun x : nat => ((p - (x + 1), 1), (x + 1, 1)). 



Lemma P2p_e_I_map : P2p_e = [fset (P2p_e_mapfun x) | x in [fsetval y in 'I_((divn (p - 1) 2))]].
Proof.
  rewrite /P2p_e /P2p. apply /eqP. rewrite eqEfsubset. apply /andP; split;
    (by_contradiction hsubset; apply (introT negPf) in hsubset; apply (elimT (fsubsetPn _ _)) in hsubset;
    destruct hsubset as [[[a1 f1] [a2 f2]] hin hnin]; apply (elimT negPf) in hnin; rewrite -hnin; clear hnin).
  - rewrite !inE /= in hin. unfold P2p_e_mapfun. 
    destruct_boolhyp hin => /= ha1 hf1 ha2 hf2 harea ha2a1 hf1f2.
    rewrite (eqnP hf1f2) /Y_area /= in harea. rewrite (eqnP hf1f2). clear hf1f2 hf1 f1.
    have hf2_1 : f2 = 1. 
      replace (a1 * f2 + a2 * f2) with (f2 * (a1 + a2)) in harea; [|by ring].
      apply (n_dvdn) in harea.
      apply (elimT primeP) in p_prime. destruct p_prime as [_ hprime]. apply hprime in harea.
      apply in_Ip in hf2. rewrite ltn_neqAle in hf2. destruct_boolhyp hf2; move => hf2 hleq.
      rewrite (negPf hf2) Bool.orb_false_r /= in harea. by apply (elimT eqnP) in harea.
    rewrite hf2_1. rewrite hf2_1 muln1 muln1 in harea.
    have ha2_0 : 0 < a2. by_contradiction ha2_0. apply (introT negPf) in ha2_0.
      rewrite -eqn0Ngt in ha2_0. rewrite (eqnP ha2_0) addn0 in harea. rewrite (eqnP harea) in ha1.
      apply in_Ip in ha1. by rewrite ltnn in ha1.
    apply /imfsetP. exists (a2 - 1).
      have hlt: a2 - 1 < ((p - 1) %/ 2). have hp : p - 1 = 2 * ((p - 1) %/ 2).
      rewrite mulnC. symmetry. apply (elimT eqP). rewrite -dvdn_eq. apply even_prime in p_prime.
      destruct p_prime as [hp | hp]; subst. have ha2' : a2 = 1 by mcnia. have ha1' : a1 = 1 by mcnia. by subst.
      rewrite dvdn2 -oddS subn1 -Lt.S_pred_pos. by []. apply (elimT leP). by apply odd_gt0.
      have hp' : p = p - 1 + 1. rewrite subn1 addn1 -Lt.S_pred_pos. by []. 
      apply (elimT leP). apply (elimT primeP) in p_prime. destruct p_prime as [hp' _]. by auto.
      rewrite hp' hp in harea. mcnia.
      by apply/imfsetP; exists (Sub (a2 - 1) hlt).
      zag_solve.
  - rewrite !inE /=. apply (elimT (imfsetP _ _ _ _)) in hin. destruct hin as [x hin heq].
    rewrite /P2p_e_mapfun in heq. inversion heq; subst.
    apply in_Imfset in hin. clear heq.
    have hxp : 2 * x < (p - 2). have pdiv2 : 2 %| (p - 1). apply even_prime in p_prime.
    destruct p_prime as [hp|hp]; subst. by []. unfold is_true in hp. rewrite dvdn2. rewrite oddB. 
    by rewrite hp /=. by apply odd_gt0. rewrite ltn_divRL in hin; [|by []].
    rewrite ltn_subRL add2n. rewrite ltn_subRL add1n leq_eqVlt in hin. destruct_boolhyp hin.
    rewrite -add2n in hin. replace (2 + (x * 2)) with (2 * (x + 1)) in hin; [|by mcnia].
    apply n_dvdn in hin. rewrite dvdn2 -oddS in pdiv2. rewrite dvdn2 in hin.
    rewrite subn1 -Lt.S_pred_pos in pdiv2. by apply (elimT negP) in hin.
    apply (elimT leP). apply (elimT primeP) in p_prime. destruct p_prime as [hp' _]. by auto.
    by rewrite mulnC.
    repeat (apply /andP; split); rewrite /Y_area /= ?muln1; try apply in_Ip; try auto; try mcnia.
Qed.

Lemma Pdp_e_card_pairs : #|`P2p_e| = (divn (p - 1) 2).
Proof.
  rewrite P2p_e_I_map. simpl. rewrite !card_imfset /=. by rewrite -cardE card_ord.
  unfold injective. move => x1 x2 h. by apply ord_inj in h.
  move => x1 x2 h. destruct (x1 == x2) eqn: heq.
    apply (elimT eqnP) in heq. by rewrite heq.
    rewrite /P2p_e_mapfun in h. inversion h. rewrite !addn1 in H1. inversion H1. by [].
Qed.

Lemma Pdp_e_card :  (modn p 4  = 1) -> ~~odd(#|`P2p_e|).
Proof.
  move => hmod. rewrite Pdp_e_card_pairs. apply mod4_halfeven in hmod.
  remember ((p - 1) %/ 2) as n. clear Heqn. rewrite modn2 in hmod.
  by rewrite -eqb0 hmod.
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
  - apply /eqP. rewrite eqEfsubset. apply /andP; split.
    + apply subset_by_in. move => [[[a1 f1] [a2 f2]] hin hnin]. rewrite !inE /= in hin.
      rewrite !in_fsetU !Bool.negb_orb !inE !Bool.negb_andb /= in hnin.
      destruct_boolhyp hin => /= ha1 hf1 ha2 hf2 harea ha2a1.
      destruct_boolhyp hnin; try mccontradiction; move => hx1 hx2 hx3.
      rewrite -leqNgt leq_eqVlt in hx1. destruct_boolhyp hx1; mccontradiction.
    + apply subset_by_in. move => [[[a1 f1] [a2 f2]] hin hnin].
      rewrite !inE !Bool.negb_andb /= in hnin. rewrite !in_fsetU !inE /= in hin.
      destruct_boolhyp hin => /= ha1 hf1 ha2 hf2 harea ha2a1;
      destruct_boolhyp hnin; mccontradiction.
  rewrite hunion. clear hunion. apply card_disjoint_triple;
    apply (elimT eqP); rewrite fsetI_eq0; apply /fdisjointP; move => [[a1 f1] [a2 f2]] hin;
    rewrite !inE /Y_area /= in hin; rewrite !inE /Y_area /=; apply (introT negP); move => hnin;
    destruct_boolhyp hin; destruct_boolhyp hnin; intros; try mccontradiction.
Qed.

Lemma P2p_g_odd : (modn p 4  = 1) -> odd #|` P2p_g |.
  move => hmod.
  have hodd := P2p_odd hmod. rewrite P2p_partition !oddD in hodd.
  by rewrite (negPf P2p_l_even) (negPf (Pdp_e_card hmod)) /= in hodd.
Qed.

(* Study of P2p_g via simple transposition                                    *)

Definition transpose_g (a : N4) : N4:= ((a.1.2,a.1.1),(a.2.2,a.2.1)).

Lemma transpose_g_involution : involutionN4 P2p_g transpose_g.
Proof.
split.
 - move => yd hin11; rewrite !inE in hin11. 
   destruct_boolhyp hin11 => h22l12  hin21l11 hin21 hin22 /eqP harea hin12 hleq.
   rewrite /transpose_l; rewrite !inE. repeat (apply /andP; split).
   by []. by []. by []. by []. rewrite -harea /Y_area; simpl. mcnia.
   by simpl. by simpl.
 - move => yd hin11; rewrite !inE in hin11.
   destruct_boolhyp hin11 => h22l12 /eqP harea hin21l11 hin21 hin22 hin12.
   rewrite /transpose_l; destruct yd as [[a1 f1] [a2 f2]]. by [].
Qed.

Lemma transpose_g_fixed : (exists (yd:N4), (yd \in (fixed_fsetN4 P2p_g transpose_g)))
                                 -> (exists a b :nat, p=a^2 + b^2).
Proof.
move => [yd hin11].
rewrite !inE in hin11; rewrite /transpose_g.
destruct_boolhyp hin11 => hyfix h22l12 h22l11 hin21 /eqP harea hin22 hin12.
move: hyfix. rewrite /transpose_g. destruct yd as [[a1 f1] [a2 f2]]. simpl.
rewrite -harea /Y_area. simpl. move=> [_ /eqP hf1 _ /eqP hf2].
exists a1; exists a2. by rewrite hf1 hf2.
Qed.

(*                                                                            *)
(* Proof of Fermat's theorem using partitions, following David Christopher    *)
(*                                                                            *)

Theorem Fermat_David_Christopher : (modn p 4 = 1) -> (exists a b :nat, p=a^2 + b^2).
Proof.
move => hk.
apply transpose_g_fixed.
apply odd_existence. 
rewrite Involution_lemma.
- by apply P2p_g_odd.
- by apply transpose_g_involution.
Qed.

End Partition_Proof.
Check Fermat_David_Christopher.

