import Mathlib  -- Needed for 'apply .. at ..' tactic
import NNG4Solutions.Define_MyNat
import NNG4Solutions.World_Algorithm_1

namespace MyNat


-- idk. Declares MyNat.add
opaque add : MyNat → MyNat → MyNat

-- Make the + operator on MyNat's invoke the MyNat.add function
instance instAdd : Add MyNat where
  add := MyNat.add

-- Axioms of addition
axiom add_zero (a : MyNat) : a + zero = a
axiom add_succ (a b : MyNat) : a + (succ b) = succ (a + b)
-- These are sufficient to define addition for any two MyNat's.
-- Example:
--             5 + 2           2 is defined as (succ 1)
--             5 + (succ 1)    add_succ
--       succ (5 + 1)          1 is defined as (succ 0)
--       succ (5 + (succ 0))   add_succ
-- succ (succ (5 + 0))         add_zero
-- succ (succ  5)              done, + is gone




theorem succ_eq_add_one (a : MyNat) : succ a = a + one := by
  -- Goal : succ a = a + one
  rw [one_eq_succ_zero]
  -- Goal : succ a = a + (succ zero)
  rw [add_succ]
  -- Goal : succ a = succ (a + zero)
  rw [add_zero]
  -- Done : succ a = succ a





-- World     :   Addition World
-- Level 1   :   zero_add

theorem zero_add (a : MyNat) : zero + a = a := by
  induction a with
  | zero =>
    -- Goal : zero + zero = zero
    rw [add_zero]
    -- Done : zero = zero
  | succ aa ha =>
    -- ha   : zero + aa = aa
    -- Goal : zero + succ aa = succ aa
    rw [add_succ]
    -- Goal : succ (zero + aa) = succ aa
    rw [ha]
    -- Done : succ aa = succ aa









-- World     :   Addition World
-- Level 2   :   succ_add

--succ a + b = succ (a + b)
theorem succ_add (a b : MyNat) : succ a + b = succ (a + b) := by
  -- Goal : succ a + b = succ (a + b)


  -- Use induction on b to split the goal into two goals:
  --   succ a + zero = succ (a + zero)
  --   and
  --   succ a + bb = succ (a + bb)   =>   succ a + succ bb = succ (a + succ bb)
  induction b with


  --
  | zero =>
    -- Goal : succ a + zero = succ (a + zero)
    repeat rw [add_zero] -- replace all (x + zero)'s with x
    -- succ a = succ a      Done.


  -- Let hb be the induction hypothesis    succ a + bb = succ (a + bb)
  | succ bb hb =>
    -- hb   : succ a + bb = succ (a + bb)
    -- Goal : succ a + succ bb = succ (a + succ bb)
    repeat rw [add_succ]
    -- Goal : succ (succ a + bb) = succ (succ (a + bb))
    rw [hb]
    -- Done







-- World     :   Addition World
-- Level 3   :   add_comm

theorem add_comm (a b : MyNat) : a + b = b + a := by
  induction a with
  | zero =>
    rw [add_zero, zero_add]
  | succ aa ha =>
    rw [succ_add, add_succ]
    rw [ha]




-- World     :   Addition World
-- Level 4   :   add_assoc

theorem add_assoc (a b c : MyNat) : a + b + c = a + (b + c) := by
  induction c with
  | zero =>
    -- Goal : a + b + zero = a + (b + zero)
    repeat rw [add_zero]
    -- Done : a + b = a + b
  | succ cc hc =>
    -- hc   : a + b + cc = a + (b + cc)
    -- Goal : a + b + succ cc = a + (b + succ cc)
    repeat rw [add_succ]
    -- Goal : succ (a + b + cc) = succ (a + (b + cc))
    rw [hc]
    -- Done : succ (a + (b + cc)) = succ (a + (b + cc))









-- World     :   Addition World
-- Level 5   :   add_right_comm

theorem add_right_comm (a b c : MyNat) : a + b + c = a + c + b := by
  rw [add_assoc]
  -- Goal : a + (b + c) = a + (c + b)
  rw [add_comm b c]
  -- Goal : a + (c + b) = a + c + b
  rw [← add_assoc]
  -- Done : a + c + b = a + c + b






-- World     :   Implication World
-- Level 5   :   x + 1 = 4   =>   x = 3

theorem implication_world_level_5 (x : MyNat) : x + one = four → x = three := by
  intro h
  -- h    : x + one = four
  -- Goal : x = three
  rw [← succ_eq_add_one] at h
  -- h    : succ x = four
  rw [four_eq_succ_three] at h
  -- h    : succ x = succ three
  apply succ_inj at h
  -- h    : x = three
  exact h
