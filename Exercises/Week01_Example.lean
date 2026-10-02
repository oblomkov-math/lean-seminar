#check 0

inductive FinSeq (α : Type) : Type where
  | empty : FinSeq α
  | push (head : α) (tail : FinSeq α) : FinSeq α

open FinSeq

def list : FinSeq Nat := push 1 (push 2 (push 5 empty))

#eval list

def concat {α : Type} (u : FinSeq α) (v : FinSeq α) : FinSeq α :=
  match u with
  | empty => v
  | push u0 u' => push u0 (concat u' v)

def reverse {α : Type} (u : FinSeq α) : FinSeq α :=
  match u with
  | empty => empty
  | push u0 u' => concat (reverse u') (push u0 empty)

#eval reverse (push 1 (push 2 (push 5 empty)))

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
