Require Coq.Vectors.Fin.
Require Import Coq.Program.Basics.

Inductive primrec : nat -> Set :=
| primrec_C {N : nat} : nat -> primrec N
| primrec_S : primrec 1
| primrec_proj {N : nat} : Fin.t N -> primrec N
| primrec_comp {K L : nat} : primrec K -> (Fin.t K -> primrec L) -> primrec L
| primrec_primrec {N : nat} : primrec N -> primrec (2+N) -> primrec (1+N)
.

Definition finhd {N : nat} (xs : (Fin.t (1+N) -> nat)) : nat := xs Fin.F1.
Definition fintail {N : nat} (xs : (Fin.t (1+N) -> nat)) : Fin.t N -> nat := compose xs Fin.FS.
Definition fincons {N : nat} (x : nat) (xs : (Fin.t N -> nat)) (i : Fin.t (1+N)) : nat :=
  match i in (Fin.t n) return (n = 1 + N -> nat) with
  | Fin.F1 n => fun _ => x
  | Fin.FS n j => fun H => xs ((eq_rec n Fin.t j N) (eq_add_S n N H))
  end eq_refl.
Local Notation "h :: t" := (fincons h t) (at level 60, right associativity).

Fixpoint primrec_interpret {K : nat} (f : primrec K) {struct f} : (Fin.t K -> nat) -> nat :=
  match f in (primrec K) return ((Fin.t K -> nat) -> nat) with
  | primrec_C N x => fun _ => x
  | primrec_S => fun xs => S (finhd xs)
  | primrec_proj _ i => fun xs => xs i
  | primrec_comp K L g hs => fun xs => primrec_interpret g (compose (fun h => primrec_interpret h xs) hs)
  | primrec_primrec N g h => fun xs =>
      nat_rec (fun _ => nat)
        (primrec_interpret g (fintail xs))
        (fun _ y => primrec_interpret h (finhd xs :: y :: fintail xs)) (finhd xs)
  end.

(* Definition by Freek, does not compile *)

Definition primrec_plus : primrec 2 :=
  primrec_primrec
    (primrec_proj 0 0) (primrec_comp primrec_S (primrec_proj 2 0)).

Lemma plus_is_primrec : @is_primrec 2 plus.
apply primrec_of with (f' := primrec_plus). intros [n m]. simpl.
rewrite plus_comm. induction m; simpl; auto.
Qed.