import NNG4Solutions.Define_MyNat
import NNG4Solutions.World_Addition
import NNG4Solutions.World_Implication

namespace MyNat



-- World     :   Advanced Addition World
-- Level 1   :   add_right_cancel

theorem add_right_cancel (a b c : MyNat) : (a + c = b + c) → a = b := by
  -- Goal : (a + c = b + c) → a = b
  intro h
  -- h    : a + c = b + c
  -- Goal : a = b
  induction c with
  | zero =>
    -- h : a + zero = b + zero
    repeat rw [add_zero] at h
    -- h : a = b
    exact h
    -- Done
  | succ cc hc =>
    -- h    : a + succ cc = b + succ cc
    -- hc   : (a + cc = b + cc) → a = b
    repeat rw [add_succ] at h
    -- h    : succ (a + cc) = succ (b + cc)
    apply succ_inj at h
    -- h    : a + cc = b + cc
    apply hc at h
    -- h    : a = b
    exact h
    -- Done






-- World     :   Advanced Addition World
-- Level 2   :   add_left_cancel

theorem add_left_cancel (a b c : MyNat) : (c + a = c + b) → a = b := by
  -- Goal : (c + a = c + b) → a = b
  rw [add_comm c a]
  rw [add_comm c b]
  -- Goal : (a + c = b + c) → a = b
  apply add_right_cancel
  -- Done





-- World     :   Advanced Addition World
-- Level 3   :   add_left_eq_self

theorem add_left_eq_self (a b : MyNat) : (a + b = b) → a = zero := by
  -- Goal : (a + b = b) → a = zero
  intro h
  -- h    : a + b = b
  -- Goal : a = zero
  induction b with
  | zero =>
    -- h    : a + zero = zero
    -- Goal : a = zero
    rw [add_zero] at h
    -- h    : a = zero
    exact h
    -- Done
  | succ bb hb =>
    -- h    : a + succ bb = succ bb
    -- hb   : a + bb = bb → a = zero
    -- Goal : a = zero
    rw [add_succ] at h
    -- h    : succ (a + bb) = succ bb
    apply succ_inj at h
    -- h    : a + bb = bb
    apply hb at h
    -- h    : a = zero
    exact h
    -- Done
    -- (instead of    apply hb at h    exact h
    --  just  'exact hb h'  also works)


  -- Way simpler proof:
  --nth_rewrite 2 [← zero_add b]
  -- Goal : (a + b = zero + b) → a = zero
  --exact add_right_cancel a 0 b






-- World     :   Advanced Addition World
-- Level 4   :   add_right_eq_self

theorem add_right_eq_self (a b : MyNat) : (b + a = b) → a = zero := by
  rw [add_comm]
  apply add_left_eq_self




-- World     :   Advanced Addition World
-- Level 5   :   add_right_eq_zero

theorem add_right_eq_zero (a b : MyNat) : a + b = zero → a = zero := by
  intro h
  -- h    : a + b = zero
  -- Goal : a = zero
  cases b with
  | zero =>
    -- Goal : a = zero
    -- h    : a + zero = zero
    rw [add_zero] at h
    -- h    : a = zero
    exact h
    -- Done
  | succ bb =>
    -- h    : a + succ bb = zero
    -- Goal : a = zero
    rw [add_succ] at h
    -- h    : succ (a + bb) = zero
    symm at h
    -- h    : zero = succ (a + bb)
    apply zero_ne_succ at h
    -- h    : False
    cases h
    -- Done  (a False statement implies any statement)






-- World     :   Advanced Addition World
-- Level 6   :   add_left_eq_zero

theorem add_left_eq_zero (a b : MyNat) : b + a = zero → a = zero := by
  rw [add_comm]
  apply add_right_eq_zero
