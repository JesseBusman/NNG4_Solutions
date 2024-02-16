import Mathlib -- Needed for symm and contrapose! tactics
import NNG4Solutions.Define_MyNat

namespace MyNat





-- World     :   Algorithm World
-- Level 5   :   succ_inj

-- WTF
def pred : MyNat → MyNat
| MyNat.zero => five         -- ?????????????????????????????????
| MyNat.succ n => n

theorem pred_succ (n : MyNat) : pred (succ n) = n := rfl

theorem succ_inj (a b : MyNat) (h : succ a = succ b) : a = b := by
  rw [← pred_succ a, h, pred_succ]






-- World     :   Algorithm World
-- Level 6   :   succ_ne_zero

def is_zero : MyNat → Prop
| MyNat.zero => True
| MyNat.succ _ => False

theorem is_zero_zero : is_zero MyNat.zero = True := rfl
theorem is_zero_succ (a : MyNat) : is_zero (MyNat.succ a) = False := rfl

theorem succ_ne_zero (a : MyNat) : succ a ≠ zero := by
  -- Goal : succ a = zero  →  False
  intro h
  -- h    : succ a = zero
  -- Goal : False
  rw [← is_zero_succ a]
  -- h    : succ a = zero
  -- Goal : is_zero (succ a)
  rw [h]
  -- Goal : is_zero zero
  rw [is_zero_zero]
  -- Goal : True
  trivial

theorem zero_ne_succ (a : MyNat) : MyNat.zero ≠ MyNat.succ a := by
  symm
  exact succ_ne_zero a






-- World     :   Algorithm World
-- Level 7   :   succ_ne_succ

theorem succ_ne_succ (a b : MyNat) : (a ≠ b) → (succ a ≠ succ b) := by
  intro h
  -- h    : a ≠ b
  -- Goal : succ a ≠ succ b
  contrapose! h
  -- h    : succ a = succ b
  -- Goal : a = b
  apply succ_inj at h
  -- h    : a = b
  exact h
