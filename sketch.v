Require Import MSetInterface.
Module RedBlackTree.
Declare Module X:OrderedType.
Definition key := X.t.


Inductive color := Red | Black.

Inductive tree :=
  | Leaf : tree
  | Node : tree -> key -> tree -> color -> tree.

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

(* inserts an element into a tree
 * needs and preserves red black binary search tree
 *)
Fixpoint insert (x:key) (t:tree) : tree := t.

(* deleets an element out of a tree
 * needs and preserves red black binary search tree
 *)
Fixpoint delete (x:key) (t:tree) : tree := t.




(** ** x is in a tree *)

Inductive isMem (x : key) : tree -> Prop :=
  | IsMemRoot : forall l y r c, X.eq x y -> isMem x (Node l y r c)
  | IsMemLeft : forall l y r c, isMem x l -> isMem x (Node l y r c)
  | IsMemRight : forall l y r c, isMem x r -> isMem x (Node l y r c).




(** ** Binary Search Tree property *)

(* all elements in s are less than x *)
Definition lt_tree x s := forall y, isMem y s -> X.lt y x.
(* all elemens in s are greater than x *)
Definition gt_tree x s := forall y, isMem y s -> X.lt x y.
 
(** [BST t] : [t] is a binary search tree
 * all in l are less than x
 * all in r are greater than x
 *)
Inductive isBST : tree -> Prop :=
  | BSTLeaf : isBST Leaf
  | BSTNode : forall x l r h, isBST l -> isBST r ->
     lt_tree x l -> gt_tree x r -> isBST (Node l x r h).



(** ** Not Red Red property *)

Inductive isBlack : tree -> Prop :=
  | IsBlackLeaf : isBlack Leaf
  | IsBlackNode : forall l x r, isBlack (Node l x r Black).

(* no two successing red nodes *)
Inductive isNotRedRed : tree -> Prop :=
  | IsBlack: forall t, isBlack t -> isNotRedRed t
  | IsNotRedRed : forall l x r, isBlack l -> isBlack r -> isNotRedRed (Node l x r Red).



(** ** Same Black Heights *)

(* "to every leaf the number of black nodes is the same" *)
Inductive isSameBlackdepth' : nat -> tree -> Prop :=
  | IsSameBlackdepthLeaf : isSameBlackdepth' O Leaf
  | IsSameBlackdepthRed   : forall n l x r, isSameBlackdepth' n l -> isSameBlackdepth' n r -> isSameBlackdepth' n (Node l x r Red)
  | IsSameBlackdepthBlack : forall n l x r, isSameBlackdepth' n l -> isSameBlackdepth' n r -> isSameBlackdepth' (S n) (Node l x r Black).

Inductive isSameBlackdepth : tree -> Prop :=
  | IsSameBlackdepth : forall t, (exists n, isSameBlackdepth' n t) -> isSameBlackdepth t.


(** ** Red Black property *)

Inductive isRedBlack : tree -> Prop :=
  | IsRedBlack : forall t, isNotRedRed t -> isSameBlackdepth t -> isRedBlack t.



(** ** Red Black Binary Search Tree *)

Inductive isRBBST : tree -> Prop :=
  | IsRBBST : forall t, isBST t -> isRedBlack t -> isRBBST t.



(** ** Proof of [mem] **)

Lemma mem_spec : forall t x `{isBST t}, mem x t = true <-> isMem x t.



(** ** Proofs of [insert] and [delete] *)

Definition stays_rbbst f := forall t, isRBBST t <-> isRBBST (f t).

(** ** Proof of [insert] *)

Lemma insert_inserts : forall x t, isMem x (insert x t).

Lemma insert_stays_rbbst : forall x, stays_rbbst (insert x).



(** ** Proof of [delete] *)

Lemma delete_deletes : forall x t, ~ isMem x (delete x t).

Lemma delete_stays_rbbst : forall x, stays_rbbst (delete x).


