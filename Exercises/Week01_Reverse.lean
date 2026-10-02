inductive FinSeq (α : Type) : Type where
  | empty : FinSeq α
  | push (head : α) (tail : FinSeq α) : FinSeq α

open FinSeq

-- make α argument explicit until after writing function
-- start with 'sorry' when writing cases
def concat {α : Type} (u : FinSeq α) (v : FinSeq α) : FinSeq α :=
  match u with
  | empty => v
  | push u0 u' => push u0 (concat u' v)

#eval concat (push 1 (push 2 empty)) (push 4 empty)

def reverse {α : Type} (u : FinSeq α) : FinSeq α :=
  match u with
  | empty => empty
  | push u0 u' => concat (reverse u') (push u0 empty)

#eval reverse (push 1 (push 2 (push 4 empty)))

-- use 'def', change later to 'theorem' to resolve warning
-- these first three are not necessary for reverse_reverse; might want to copy/paste?
theorem push_nonempty {α : Type} {x : α} {u : FinSeq α} : push x u ≠ empty :=
  fun h => nomatch h

theorem concat_nonempty_left {α : Type} (u : FinSeq α) (v : FinSeq α) (hu : u ≠ empty) : concat u v ≠ empty :=
  match u with
  | empty => nomatch hu
  | push _ _ => push_nonempty

theorem concat_nonempty_right {α : Type} (u : FinSeq α) (v : FinSeq α) (hv : v ≠ empty) : concat u v ≠ empty :=
  match u with
  | empty => hv
  | push _ _ => push_nonempty

theorem last_to_first {α : Type} (u : FinSeq α) (x : α) : reverse (concat u (push x empty)) = push x (reverse u) :=
  match u with
  | empty => rfl
  | push u0 u' => by
    unfold concat
    unfold reverse
    rw [last_to_first]
    rfl

theorem reverse_reverse {α : Type} (u : FinSeq α) : reverse (reverse u) = u :=
  match u with
  | empty => rfl
  | push u0 u' => by
    have unf : reverse (push u0 u') = concat (reverse u') (push u0 empty) := rfl
    rw [unf]
    rw [last_to_first]
    rw [reverse_reverse]

-- same but with induction tactic
theorem reverse_reverse_2 {α : Type} (u : FinSeq α) : reverse (reverse u) = u := by
  induction u with
  | empty => rfl
  | push u0 u' indh =>
    have unf : reverse (push u0 u') = concat (reverse u') (push u0 empty) := rfl
    rw [unf, last_to_first]
    rw [indh]

-- explain occurence of 'by': term mode vs tactic mode
-- show how you can also use 'match' in tactic mode: modify reverse_reverse
-- show alternative definition of 'FinSeq' without 'head' and 'tail'; explain currying

#check List -- go to defintion; explain universes?
#check 1 :: 2 :: 3 :: []
#check [1, 2, 3]
#check List.append
#check List.reverse
#check List.reverse_reverse
