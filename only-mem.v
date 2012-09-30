Require Import MSetInterface.
Module RedBlackTree.
Declare Module X:OrderedType.
Definition key := X.t.


Inductive color := Red | Black.

Inductive tree :=
  | Leaf : tree
  | Node : tree -> key -> tree -> color -> tree.

(** ** Membership *)

(** The [mem] function is deciding membership. It exploits the
    binary search tree invariant to achieve logarithmic complexity. *)

Fixpoint mem x s :=
   match s with
     |  Leaf => false
     |  Node l y r _ => match X.compare x y with
             | Lt => mem x l
             | Eq => true
             | Gt => mem x r
         end
   end.

Inductive InT (x : key) : tree -> Prop :=
  | IsRoot : forall l y r c, X.eq x y -> InT x (Node l y r c)
  | InLeft : forall l y r c, InT x l -> InT x (Node l y r c)
  | InRight : forall l y r c, InT x r -> InT x (Node l y r c).

(** ** Binary search trees *)

(** [lt_tree x s]: all elements in [s] are smaller than [x]
   (resp. greater for [gt_tree]) *)

Definition lt_tree x s := forall y, InT y s -> X.lt y x.
Definition gt_tree x s := forall y, InT y s -> X.lt x y.
 
(** [bst t] : [t] is a binary search tree *)

Inductive bst : tree -> Prop :=
  | BSLeaf : bst Leaf
  | BSNode : forall x l r h, bst l -> bst r ->
     lt_tree x l -> gt_tree x r -> bst (Node l x r h).

(* XXX this is for proper naming of hypotheses with H and a number, isnt it? *)
Class Ok (s:tree) : Prop := ok : bst s.
Instance bst_Ok s (Hs : bst s) : Ok s := { ok := Hs }.
(**)

(** Proof of [mem] **)
Module Import MX := OrderedTypeFacts X.

Lemma lt_leaf : forall x : key, lt_tree x Leaf.
Proof.
 red; inversion 1.
Qed.

Lemma lt_tree_not_in :
 forall (x : key) (t : tree), lt_tree x t -> ~ InT x t.
Proof.
 intros. intro. generalize (H _ H0). MX.order.
Qed.

Lemma mem_spec : forall s x `{Ok s}, mem x s = true <-> InT x s.
Proof.
 constructor.
  induction s as [|l IHl x' r IHr].
   simpl. intro. discriminate. 
   simpl. intro. destruct (X.compare_spec x x').
    inversion_clear H. constructor. trivial.
    inversion_clear H. apply InLeft. apply IHl. exact H2. exact H0.
    inversion_clear H. apply InRight. apply IHr. exact H3. exact H0.
  induction s as [|l Ihl x' r IHr].
   simpl. intro. contradict H0. apply lt_tree_not_in. apply lt_leaf. 
   simpl. intro. destruct (X.compare_spec x x').
    trivial.
    inversion_clear H. inversion_clear H0.
     MX.order.
     apply Ihl. exact H2. exact H.
     generalize (H5 _ H). MX.order.
     inversion_clear H. inversion_clear H0.
      MX.order.
      generalize (H4 _ H). MX.order.
      apply IHr. exact H3. exact H.
Qed.   
