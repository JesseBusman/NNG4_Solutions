-- Define a new type called MyNat with two constructors
inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat

-- Define some numbers
def zero  : MyNat := MyNat.zero
def one   : MyNat := MyNat.succ zero
def two   : MyNat := MyNat.succ one
def three : MyNat := MyNat.succ two
def four  : MyNat := MyNat.succ three
def five  : MyNat := MyNat.succ four

namespace MyNat

theorem one_eq_succ_zero   : one   = MyNat.succ zero  := rfl
theorem two_eq_succ_one    : two   = MyNat.succ one   := rfl
theorem three_eq_succ_two  : three = MyNat.succ two   := rfl
theorem four_eq_succ_three : four  = MyNat.succ three := rfl
theorem five_eq_succ_four  : five  = MyNat.succ four  := rfl

-- idk.
instance : Inhabited MyNat where
  default := MyNat.zero

/-
-- Use OfNat to allow number literals to be converted into MyNat's
def ofNat (x : Nat) : MyNat :=
  match x with
  | Nat.zero   => MyNat.zero
  | Nat.succ b => MyNat.succ (ofNat b)

instance instofNat {n : Nat} : OfNat MyNat n where
  ofNat := ofNat n
-/
