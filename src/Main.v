(* Euclid's proof that prime numbers are infinite.
   Frédéric Blanqui INRIA, 25 November 2014. *)

Set Implicit Arguments.

Require Import Arith Omega.

Lemma mult_gt_0 a b : a * b > 0 <-> a > 0 /\ b > 0.

Proof.
  (* We proceed by case on a and b. *)
  destruct a. omega. destruct b. omega. split. omega.
  intros _. simpl. (*omega does not work here!*) apply gt_Sn_O.
Qed.

Lemma le_mult_r a b : b > 0 -> a <= a * b.

Proof.
  intros hb. rewrite <- (mult_1_r a) at 1. apply mult_le_compat_l. omega.
Qed.

(** Divisibility. *)

Definition divide a b := exists q, b = a * q.

Infix "\" := divide (at level 70).

Lemma divide_le a b : b > 0 -> a \ b -> a <= b.

Proof.
  intros b_gt_0 [q ha]. subst. apply le_mult_r. rewrite mult_gt_0 in b_gt_0.
  tauto.
Qed.

Lemma divide_mult_l a b c : a \ b -> a \ c * b.

Proof. intros [q ha]. subst. exists (q*c). ring. Qed.

Lemma divide_minus a b c : a \ b -> a \ c -> a \ b-c.

Proof.
  intros [p hb] [q hc]. subst. exists (p-q). (* omega does not work here! *)
  rewrite <- mult_minus_distr_l. reflexivity.
Qed.

Lemma divide_trans a b c : a \ b -> b \ c -> a \ c.

Proof. intros [q h] [r g]. exists (q * r). subst. ring. Qed.

(* Product of a list of natural numbers. *)

Require Import List.

Fixpoint prod l :=
  match l with
    | nil => 1
    | a :: l' => a * prod l'
  end.

Lemma prod_gt_0 : forall l, ~In 0 l <-> prod l > 0.

Proof. induction l; simpl. omega. rewrite mult_gt_0. intuition. Qed.

Lemma in_prod {a} : forall {l}, ~In 0 l -> In a l -> a <= prod l.

Proof.
  (* We proceed by induction on l. *)
  induction l as [|b l hl]; simpl.
  omega.
  intros hb [ha|ha].
  subst. apply le_mult_r. apply prod_gt_0. tauto.
  rewrite <- (mult_1_l a) at 1. apply mult_le_compat. omega. tauto.
Qed.

Lemma divide_prod {a} : forall {l}, In a l -> a \ prod l.

Proof.
  (* We proceed by induction on l. *)
  induction l as [|b l hl]; simpl.
  tauto.
  intros [ha|ha].
  subst. exists (prod l). reflexivity.
  apply divide_mult_l. tauto.
Qed.

(* Prime numbers. *)

Definition prime b := b >= 2 /\ forall a, divide a b -> a = 1 \/ a = b.

Lemma zero_isnt_prime : ~prime 0.

Proof. unfold prime. omega. Qed.

Theorem fundamental_theorem_of_arithmetic a :
  a >= 2 -> exists p, prime p /\ p \ a.

Proof.
  (* We proceed by well-founded induction on a. *)
  pattern a; apply lt_wf_ind; clear a; intros a IHa a_ge_2.
  Require Import Classical.
  destruct (classic (prime a)) as [a_is_prime|a_isnt_prime].
  (* If a is prime, then we can take p=a. *)
  exists a. intuition. exists 1. ring.
  (* If a is not prime, then there is some b between 2 and a-1 that divides a. *)
  apply not_and_or in a_isnt_prime. intuition. apply not_all_ex_not in H.
  destruct H as [b hb]. apply imply_to_and in hb. destruct hb as [b_div_a hb].
  apply not_or_and in hb.
  assert (b_lt_a : b < a). apply divide_le in b_div_a. omega. omega.
  assert (b_ge_2 : b >= 2). destruct b_div_a as [q ha].
  destruct (eq_nat_dec b 0). 2: omega. subst. omega.
  (* By induction hypothesis on b, there is some prime p that divides b,
  and thus a by transitivity. *)
  destruct (IHa _ b_lt_a b_ge_2) as [p [p_prime p_div_b]].
  exists p. intuition. apply divide_trans with b; assumption.
Qed.

Theorem primes_are_infinite : ~ (exists l, forall a, prime a <-> In a l).

Proof.
  intros [l all_primes_in_l]. set (n := S (prod l)).
  (* We prove that n is prime. *)
  assert (n_is_prime : prime n). split.
  (* n >= 2 *)
  apply le_n_S. apply lt_le_S. apply prod_gt_0.
  rewrite <- all_primes_in_l. apply zero_isnt_prime.
  (* We now prove that assuming that there is a divider a of n that is
  different from 1 and n leads to a contradiction. *)
  intros a a_div_n. destruct (eq_nat_dec a 1). tauto.
  right. destruct (eq_nat_dec a n). assumption. apply False_rec.
  (* We prove that a is >= 2. *)
  assert (a_ge_2 : a >= 2). destruct a_div_n as [q hn].
  destruct (eq_nat_dec a 0). subst. rewrite mult_0_l in hn. omega. omega.
  (* Hence, a has a prime divider p. *)
  destruct (fundamental_theorem_of_arithmetic a_ge_2) as [p [p1 p2]].
  (* By transitivity, p divides n. *)
  generalize (divide_trans p2 a_div_n); intro p_div_n.
  (* Since all primes are in l, p is in l and p divides prod l. *)
  assert (p_in_l : In p l). rewrite <- all_primes_in_l. assumption.
  apply divide_prod in p_in_l.
  (* Thus p divides n-prod l=1. *)
  generalize (divide_minus p_div_n p_in_l).
  unfold n. rewrite <- minus_Sn_m, minus_diag. 2: reflexivity.
  (* Therefore p=1 but 1 is not prime. Hence, n is prime. *)
  intros [q hp]. symmetry in hp. apply mult_is_one in hp. destruct hp. subst.
  destruct p1. omega.
  (* We now prove that n is not in l. *)
  rewrite all_primes_in_l in n_is_prime.
  assert (zero_notin_l : ~In 0 l).
  rewrite <- all_primes_in_l. unfold prime. omega.
  generalize (in_prod zero_notin_l n_is_prime). unfold n. omega.
Qed.
