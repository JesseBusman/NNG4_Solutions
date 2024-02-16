import NNG4Solutions.Define_MyNat
import NNG4Solutions.World_Addition


namespace MyNat




-- idk. Declares MyNat.mul
opaque mul : MyNat → MyNat → MyNat





-- Make the * operator on MyNat's invoke the MyNat.mul function
instance instMul : Mul MyNat where
  mul := MyNat.mul





-- Axioms of multiplication
axiom mul_zero (a : MyNat) : a * zero = zero
axiom mul_succ (a b : MyNat) : a * (succ b) = a * b + a




-- World     :   Multiplication World
-- Level 1   :   mul_one

theorem mul_one (a : MyNat) : a * one = a := by
  -- Goal : a * one = a
  rw [one_eq_succ_zero]
  -- Goal : a * succ zero = a
  rw [mul_succ]
  -- Goal : a * zero + a = a
  rw [mul_zero]
  -- Goal : zero + a = a
  rw [zero_add]
  -- Done : a = a




-- World     :   Multiplication World
-- Level 2   :   zero_mul

theorem zero_mul (a : MyNat) : zero * a = zero := by
  induction a with
  | zero =>
    rw [mul_zero]
  | succ aa ha =>
    -- ha   : zero * aa = zero
    -- Goal : zero * succ aa = zero
    rw [mul_succ]
    -- Goal : zero * aa + zero = zero
    rw [add_zero]
    -- Goal : zero * aa = zero
    exact ha






-- World     :   Multiplication World
-- Level 3   :   succ_mul

theorem succ_mul (a b : MyNat) : succ a * b = a * b + b := by
  induction b with
  | zero =>
    -- Goal : succ a * zero = a * zero + zero
    rw [mul_zero, add_zero, mul_zero]
    -- Done : zero = zero
  | succ bb hb =>
    -- hb   : succ a * bb = a * bb + bb
    -- Goal : succ a * succ bb = a * succ bb + succ bb
    rw [mul_succ]
    -- succ a * bb + succ a = a * succ bb + succ bb
    rw [mul_succ]
    -- succ a * bb + succ a = a * bb + a + succ bb
    repeat rw [add_succ]
    -- Goal : succ (succ a * bb + a) = succ (a * bb + a + bb)
    induction a with
    | zero =>
      -- hb   : succ zero * bb = zero * bb + bb
      repeat rw [add_zero]
      -- Goal : succ (succ zero * bb) = succ (zero * bb + bb)
      rw [hb]
      -- Done : succ (zero * bb + bb) = succ (zero * bb + bb)
    | succ f =>
      -- hb   : succ (succ f) * bb = succ f * bb + bb
      -- Goal : succ (succ (succ f) * bb + succ f) = succ (succ f * bb + succ f + bb)
      repeat rw [add_succ]
      -- Goal : succ (succ (succ (succ f) * bb + f)) = succ (succ (succ f * bb + f) + bb)
      repeat rw [succ_add]
      -- Goal : succ (succ (succ (succ f) * bb + f)) = succ (succ (succ f * bb + f + bb))
      rw [add_assoc]
      -- Goal : succ (succ (succ (succ f) * bb + f)) = succ (succ (succ f * bb + (f + bb)))
      rw [add_comm f bb]
      -- Goal : succ (succ (succ (succ f) * bb + f)) = succ (succ (succ f * bb + (bb + f)))
      rw [← add_assoc]
      -- Goal : succ (succ (succ (succ f) * bb + f)) = succ (succ (succ f * bb + bb + f))
      rw [hb]
      -- Done : succ (succ (succ f * bb + bb + f)) = succ (succ (succ f * bb + bb + f))
-- Not my best work 😬




-- World     :   Multiplication World
-- Level 4   :   mul_comm

theorem mul_comm (a b : MyNat) : a * b = b * a := by
  induction a with
  | zero =>
    -- Goal : zero * b = b * zero
    rw [mul_zero, zero_mul]
    -- Done : zero = zero
  | succ aa ha =>
    -- ha   : aa * b = b * aa
    -- Goal : succ aa * b = b * succ aa
    rw [mul_succ, succ_mul]
    -- Goal : aa * b + b = b * aa + b
    rw [ha]
    -- Done : b * aa + b = b * aa + b




-- World     :   Multiplication World
-- Level 5   :   one_mul

theorem one_mul (a : MyNat) : one * a = a := by
  rw [mul_comm, mul_one]




-- World     :   Multiplication World
-- Level 6   :   two_mul

theorem two_mul (a : MyNat) : two * a = a + a := by
  -- Goal : two * a = a + a
  rw [two_eq_succ_one]
  -- Goal : succ one * a = a + a
  rw [succ_mul]
  -- Goal : one * a + a = a + a
  rw [one_mul]
  -- Done : a + a = a + a



-- World     :   Multiplication World
-- Level 7   :   mul_add

theorem mul_add (a b c : MyNat) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero =>
    -- Goal : a * (b + zero) = a * b + a * zero
    rw [add_zero, mul_zero, add_zero]
    -- Done : a * b = a * b
  | succ cc hc =>
    -- hc   : a * (b + cc) = a * b + a * cc
    -- Goal : a * (b + succ cc) = a * b + a * succ cc
    rw [add_succ]
    -- Goal : a * succ (b + cc) = a * b + a * succ cc
    repeat rw [mul_succ]
    -- Goal : a * (b + cc) + a = a * b + (a * cc + a)
    rw [← add_assoc]
    -- Goal : a * (b + cc) + a = a * b + a * cc + a
    rw [hc]
    -- Done : a * b + a * cc + a = a * b + a * cc + a







-- World     :   Multiplication World
-- Level 8   :   mul_add

theorem add_mul (a b c : MyNat) : (a + b) * c = a * c + b * c := by
  -- Goal : (a + b) * c = a * c + b * c
  rw [mul_comm]
  -- Goal : c * (a + b) = a * c + b * c
  rw [mul_add]
  -- Goal : c * a + c * b = a * c + b * c
  rw [mul_comm a c, mul_comm c b]
  -- Done : a * c + b * c = a * c + b * c





-- World     :   Multiplication World
-- Level 9   :   mul_assoc

theorem mul_assoc (a b c : MyNat) : (a * b) * c = a * (b * c) := by
  induction b with
  | zero =>
    -- Goal : a * zero * c = a * (zero * c)
    rw [zero_mul, mul_zero, zero_mul]
    -- Done : zero = zero
  | succ bb hb =>
    -- hb   : a * bb * c = a * (bb * c)
    -- Goal : a * succ bb * c = a * (succ bb * c)
    rw [mul_succ, succ_mul]
    -- Goal : (a * bb + a) * c = a * (bb * c + c)
    rw [add_mul, mul_add]
    -- Goal : a * bb * c + a * c = a * (bb * c) + a * c
    rw [hb]
    -- Done : a * (bb * c) + a * c = a * (bb * c) + a * c
