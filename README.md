# Zagier_project
Formal verification of Zagier's one-sentence proof of Fermat's Theorem and related proofs.

The code can be run either in one block (all_proofs.v) or as four separate files (see folder Separate_files).
The file lemmata.v contains the prerequisites and should be compiled first.
proof_A_Zagier.v contains Zagier's one-sentence proof.
proof_B_partitions.v contains another short proof of Fermat's theorem.
proof_C_Jackson contains a proof of another related result, following Zagier's approach.

Required: Coq 8.13.0 and Mathcomp 1.12.0 or later versions.

The project is presented in the paper "Formal verification of Zagier's one-sentence proof"
https://arxiv.org/abs/2103.11389
