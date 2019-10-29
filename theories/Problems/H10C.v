(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

From Undecidability.H10C Require Export h10c_defs.

Set Implicit Arguments.

Local Notation "〚 c 〛" := (h10c_sem c).

Definition H10C_PROBLEM := list h10c.
Definition H10C_SAT (l : H10C_PROBLEM) := exists φ, forall c, In c l ->〚c〛φ.

About H10C_SAT.


