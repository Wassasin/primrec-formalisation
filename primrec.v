Require Coq.Vectors.Fin.
Require Import Coq.Program.Basics.

Inductive primrec : nat -> Set :=
| primrec_C {N : nat} : nat -> primrec N
| primrec_S : primrec 1
| primrec_proj {N : nat} : Fin.t N -> primrec N
| primrec_comp {K L : nat} : primrec K -> (Fin.t K -> primrec L) -> primrec L
| primrec_primrec {N : nat} : primrec N -> primrec (2+N) -> primrec (1+N)
.

Definition finnil {A : Type} (bot : A) : Fin.t 0 -> A := fun _ => bot.
Definition finhd {A : Type} {N : nat} (xs : (Fin.t (1+N) -> A)) : A := xs Fin.F1.
Definition fintail {A : Type} {N : nat} (xs : (Fin.t (1+N) -> A)) : Fin.t N -> A := compose xs Fin.FS.
Definition fincons {A : Type} {N : nat} (x : A) (xs : (Fin.t N -> A)) (i : Fin.t (1+N)) : A :=
  match i in (Fin.t n) return (n = 1 + N -> A) with
  | Fin.F1 n => fun _ => x
  | Fin.FS n j => fun H => xs ((eq_rec n Fin.t j N) (eq_add_S n N H))
  end eq_refl.
Local Notation "h :: t" := (fincons h t) (at level 60, right associativity).

Definition finnilnat := finnil 0.

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

Definition ftype_gen (A B : Type) : nat -> Type := nat_rect (fun _ => Type) B (fun _ IHX => arrow A IHX).
Definition ftype : nat -> Type : Type := ftype_gen nat nat.

Fixpoint fconv {N : nat} (f : ftype N) {struct N} : (Fin.t N -> nat) -> nat :=
  fun xs => match N as n return (ftype n -> (Fin.t n -> nat) -> nat) with
  | 0 => fun f _ => f
  | S N => fun f xs => fconv (f (xs Fin.F1)) (compose xs Fin.FS)
  end f xs.

Definition ftype_compose {N : nat} {A B C : Type} (g : B -> C) (f : ftype_gen A B N) : (ftype_gen A C N) :=
  nat_rect (fun N => ftype_gen A B N -> ftype_gen A C N) g (fun N IHcomp f x => IHcomp (f x)) N f.

Fixpoint construct {N : nat} : ftype_gen nat (Fin.t N -> nat) N :=
  match N as N return (ftype_gen nat (Fin.t N -> nat) N) with
   | 0 => finnilnat
   | S N => fun x => ftype_compose (fincons x) construct
   end.

Definition fconv_inv {N : nat} (f : (Fin.t N -> nat) -> nat) : ftype N := ftype_compose f construct.

Inductive is_primrec {N : nat} : ftype N -> Prop :=
| function_is_primrec : forall f : ftype N, forall g : primrec N, forall xs : Fin.t N -> nat, (fconv f) xs = (primrec_interpret g) xs -> is_primrec f.

Definition primrec_plus : primrec 2 :=
  primrec_primrec
    (primrec_proj Fin.F1) (primrec_comp primrec_S ((primrec_proj (Fin.FS Fin.F1)) :: finnil (primrec_C 0))).

Require Import Arith.Plus.

Variable x y : nat.

Lemma plus_is_primrec : @is_primrec 2 plus.
apply (@function_is_primrec 2 plus primrec_plus (x :: y :: finnilnat)).
simpl. unfold finhd. unfold fintail. unfold compose. simpl.

rewrite plus_comm.
unfold nat_rec.
unfold nat_rect.

induction x.
auto.
inversion_clear IHn.
simpl.
auto.
Qed.
