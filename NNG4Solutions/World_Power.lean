import NNG4Solutions.Define_MyNat
import NNG4Solutions.World_Addition
import NNG4Solutions.World_Multiplication

namespace MyNat


-- idk. Declares MyNat.pow
namespace MyNat
opaque pow : MyNat → MyNat → MyNat





-- Make the * operator on MyNat's invoke the MyNat.pow function
instance instPow : Pow MyNat MyNat where
  pow := MyNat.pow




-- Axioms of power
axiom pow_zero (a : MyNat) : a ^ zero = one
axiom pow_succ (a b : MyNat) : a ^ (succ b) = (a ^ b) * a




-- World     :   Power World
-- Level 1   :   zero_pow_zero

theorem zero_pow_zero : zero ^ zero = one := by
  -- Goal : zero ^ zero = one
  rw [pow_zero]
  -- Done : one = one




-- World     :   Power World
-- Level 2   :   zero_pow_succ

theorem zero_pow_succ (a : MyNat) : zero ^ (succ a) = zero := by
  -- Goal : zero ^ (succ a) = zero
  rw [pow_succ]
  -- Goal : zero ^ a * zero = zero
  rw [mul_zero]
  -- Done : zero = zero




-- World     :   Power World
-- Level 3   :   pow_one

theorem pow_one (a : MyNat) : a ^ one = a := by
  rw [one_eq_succ_zero]
  -- Goal : a ^ succ zero = a
  rw [pow_succ]
  -- Goal : a ^ zero * a = a
  rw [pow_zero]
  -- Goal : one * a = a
  rw [one_mul]
  -- Done : a = a




-- World     :   Power World
-- Level 4   :   one_pow

theorem one_pow (a : MyNat) : one ^ a = one := by
  induction a with
  | zero =>
    -- Goal : one ^ zero = one
    rw [pow_zero]
    -- Done : one = one
  | succ aa ha =>
    -- ha   : one ^ aa = one
    -- Goal : one ^ succ aa = one
    rw [pow_succ]
    -- Goal : one ^ aa * one = one
    rw [mul_one, ha]
    -- Done : one = one





-- World     :   Power World
-- Level 5   :   pow_two

theorem pow_two (a : MyNat) : a ^ two = a * a := by
  -- Goal : a ^ two = a * a
  rw [two_eq_succ_one]
  -- Goal : a ^ succ one = a * a
  rw [pow_succ]
  -- Goal : a ^ one * a = a * a
  rw [pow_one]
  -- Done : a * a = a * a





-- World     :   Power World
-- Level 6   :   pow_add

theorem pow_add (a b c : MyNat) : a ^ (b + c) = a ^ b * a ^ c := by
  induction c with
  | zero =>
    -- Goal : a ^ (b + zero) = a ^ b * a ^ zero
    rw [add_zero, pow_zero, mul_one]
    -- Done : a ^ b = a ^ b
  | succ cc hc =>
    -- hc   : a ^ (b + cc) = a ^ b * a ^ cc
    -- Goal : a ^ (b + succ cc)  = a ^ b * a ^ succ cc
    rw [add_succ]
    -- Goal : a ^ succ (b + cc)  = a ^ b * a ^ succ cc
    rw [pow_succ]
    -- Goal : a ^ (b + cc) * a   = a ^ b * a ^ succ cc
    rw [pow_succ]
    -- Goal : a ^ (b + cc) * a   = a ^ b * (a ^ cc * a)
    rw [hc]
    -- Goal : a ^ b * a ^ cc * a = a ^ b * (a ^ cc * a)
    rw [mul_assoc]
    -- Done




-- World     :   Power World
-- Level 7   :   mul_pow

theorem mul_pow (a b c : MyNat) : (a * b) ^ c = a ^ c * b ^ c := by
  induction c with
  | zero =>
    -- Goal : (a * b) ^ zero = a ^ zero * b ^ zero
    repeat rw [pow_zero]
    -- Goal : one = one * one
    rw [mul_one]
    -- Done : one = one
  | succ cc hc =>
    -- hc   : (a * b) ^ cc = a ^ cc * b ^ cc
    -- Goal : (a * b) ^ succ cc = a ^ succ cc * b ^ succ cc
    repeat rw [pow_succ]
    -- Goal : (a * b) ^ cc * (a * b) = a ^ cc * a * (b ^ cc * b)
    repeat rw [← mul_assoc]
    -- Goal : (a * b) ^ cc *  a * b  = a ^ cc * a *  b ^ cc * b
    rw [hc]
    -- Goal : a ^ cc *  b ^ cc * a  * b = a ^ cc * a * b ^ cc * b
    rw [mul_assoc (a ^ cc)]
    -- Goal : a ^ cc * (b ^ cc * a) * b = a ^ cc * a * b ^ cc * b
    rw [mul_comm (b ^ cc) a]
    -- Goal : a ^ cc * (a * b ^ cc) * b = a ^ cc * a * b ^ cc * b
    rw [← mul_assoc]
    -- Done : a ^ cc *  a * b ^ cc  * b = a ^ cc * a * b ^ cc * b





-- World     :   Power World
-- Level 8   :   pow_pow

theorem pow_pow (a b c : MyNat) : (a ^ b) ^ c = a ^ (b * c) := by
  induction c with
  | zero =>
    -- Goal : (a ^ b) ^ zero = a ^ (b * zero)
    rw [mul_zero, pow_zero, pow_zero]
    -- Done : one = one
  | succ cc hc =>
    -- hc   : (a ^ b) ^ cc = a ^ (b * cc)
    -- Goal : (a ^ b) ^ succ cc = a ^ (b * succ cc)
    rw [pow_succ]
    -- Goal : (a ^ b) ^ cc * a ^ b = a ^ (b * succ cc)
    rw [mul_succ]
    -- Goal : (a ^ b) ^ cc * a ^ b = a ^ (b * cc + b)
    rw [hc]
    -- Goal : a ^ (b * cc) * a ^ b = a ^ (b * cc + b)
    rw [pow_add]
    -- Done : a ^ (b * cc) * a ^ b = a ^ (b * cc) * a ^ b





-- World     :   Power World
-- Level 9   :   add_sq

theorem add_sq (a b : MyNat) : (a + b) ^ two = (a ^ two) + (b ^ two) + (two * a * b) := by
  repeat rw [pow_two]
  -- Goal : (a + b) * (a + b) = a * a + b * b + two * a * b
  rw [mul_add, add_mul, add_mul]
  -- Goal : a * a + b * a + (a * b + b * b) =
  --        a * a + b * b + two * a * b
  rw [two_mul]
  -- Goal : a * a + b * a + (a * b + b * b) =
  --        a * a + b * b + (a + a) * b
  repeat rw [add_mul]
  -- Goal : a * a + b * a + (a * b + b * b) =
  --        a * a + b * b + (a * b + a * b)
  repeat rw [← add_assoc]
  -- Goal : a * a + b * a + a * b + b * b =
  --        a * a + b * b + a * b + a * b
  rw [add_right_comm]
  -- Goal : a * a + b * a + b * b + a * b =
  --        a * a + b * b + a * b + a * b
  rw [add_right_comm (a*a) (b*a)]
  -- Goal : a * a + b * b + b * a + a * b =
  --        a * a + b * b + a * b + a * b
  rw [mul_comm b a]
  -- Done : a * a + b * b + a * b + a * b =
  --        a * a + b * b + a * b + a * b






-- World     :   Power World
-- Level 10  :   Fermat's Last Theorem

theorem fermat_last_theorem (a b c n : MyNat) : (a+one)^(n+three) + (b+one)^(n+three) ≠ (c+one)^(n+three) := by
  sorry
