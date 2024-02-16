import NNG4Solutions.Define_MyNat
import NNG4Solutions.World_Addition
import NNG4Solutions.World_AdvancedAddition
import NNG4Solutions.World_Implication
import NNG4Solutions.World_Multiplication
import NNG4Solutions.World_LeqWorld

namespace MyNat







-- World     :   Advanced Multiplication World
-- Level 1   :   mul_le_mul_right

theorem mul_le_mul_right (a b c : MyNat) : a ≤ b → a * c ≤ b * c := by
  intro h
  -- h    : a ≤ b
  -- Goal : a * c ≤ b * c
  cases h with
  | intro hh hhh =>
    -- hhh  : b = a + hh
    rw [hhh]
    -- Goal : a * c ≤ (a + hh) * c
    use (hh * c)
    -- Goal : (a + hh) * c = a * c + hh * c
    rw [add_mul]
    -- Done : a * c + hh * c = a * c + hh * c



-- World     :   Advanced Multiplication World
-- Level 2   :   mul_left_ne_zero

theorem mul_left_ne_zero (a b : MyNat) : (a * b ≠ zero) → a ≠ zero := by
  intro h
  -- h    : a * b ≠ zero
  -- Goal : a ≠ zero
  intro hb
  -- hb   : a = zero
  -- Goal : False
  apply h
  -- Goal : a * b = zero
  rw [hb]
  -- Goal : zero * b = zero
  rw [zero_mul]
  -- Done : zero = zero





-- World     :   Advanced Multiplication World
-- Level 3   :   eq_succ_of_ne_zero

theorem eq_succ_of_ne_zero (a : MyNat) : (a ≠ zero) → (∃ n, a = succ n) := by
  intro ha
  cases a with
  | zero =>
    -- ha   : zero ≠ zero
    tauto -- tauto is smart.
  | succ aa =>
    -- ha   : succ aa ≠ zero
    -- Goal : ∃ n, succ aa = succ n
    use aa
    -- Done : succ aa = succ aa




-- World     :   Advanced Multiplication World
-- Level 4   :   one_le_of_ne_zero

theorem one_le_of_ne_zero (a : MyNat) : (a ≠ zero) → (one ≤ a) := by
  intro ha
  -- ha   : a ≠ zero
  -- Goal : one ≤ a
  apply eq_succ_of_ne_zero at ha
  -- ha   : ∃ n, a = succ n
  cases a with
  | zero =>
    -- ha   : ∃ n, zero = succ n
    tauto
  | succ aa =>
    -- Goal : one ≤ succ aa       (which is short for:     ∃ n, succ aa = one + n)
    use aa
    -- Goal : succ aa = one + aa
    rw [add_comm]
    -- Goal : succ aa = aa + one
    rw [succ_eq_add_one]
    -- Done : aa + one = aa + one







-- World     :   Advanced Multiplication World
-- Level 5   :   le_mul_right

theorem le_mul_right (a b : MyNat) : (a * b ≠ zero) → (a ≤ a * b) := by
  intro h
  -- h    : a * b ≠ zero
  -- Goal : a ≤ a * b
  cases a with
  | zero =>
    -- Goal : zero ≤ zero * b
    apply zero_le
  | succ aa =>
    -- h    : succ aa * b ≠ zero
    rw [mul_comm] at h
    -- h    : b * succ aa ≠ zero
    apply mul_left_ne_zero at h
    -- h    : b ≠ zero
    -- Goal : succ aa ≤ aa * b + b
    cases b with
    | zero =>
      tauto
    | succ bb =>
      rw [mul_succ]
      -- Goal : succ aa ≤ succ aa * bb + succ aa
      apply le_add_self

-- Game gives much better solution:
theorem le_mul_right_better (a b : MyNat) : (a * b ≠ zero) → (a ≤ a * b) := by
  intro h
  -- h    : a * b ≠ zero
  -- Goal : a ≤ a * b
  rw [mul_comm] at h
  -- h    : a * b ≠ zero
  apply mul_left_ne_zero at h
  -- h    : b ≠ zero
  apply one_le_of_ne_zero at h
  -- h    : one ≤ b
  apply mul_le_mul_right one b a at h
  -- h    : one * a ≤ b * a
  rw [one_mul, mul_comm] at h
  -- h    : a ≤ a * b
  exact h








-- World     :   Advanced Multiplication World
-- Level 6   :   mul_right_eq_one

theorem mul_right_eq_one (a b : MyNat) : (a * b = one) → a = one := by
  intro h
  -- Goal : a = one
  -- h    : a * b = one
  have h2 : a * b ≠ zero := by  -- 'have h2'  basically just creates a theorem called h2, scoped to the current theorem.
    rw [h]
    tauto
  -- h2   : a * b ≠ zero
  apply le_mul_right at h2
  -- h2   : a ≤ a * b
  rw [h] at h2
  -- h2   : a ≤ one
  apply le_one at h2
  -- h2   : a = zero   ∨   a = one
  cases h2 with
  | inl h0 =>
    -- h0   : a = zero
    rw [h0] at h
    -- h    : zero * b = one
    rw [zero_mul] at h
    -- h    : zero = one
    tauto            -- the a = zero case has been disproven by contradiction.
  | inr h1 =>
    -- h1   : a = one
    exact h1





-- World     :   Advanced Multiplication World
-- Level 7   :   mul_ne_zero

theorem mul_ne_zero (a b : MyNat) : (a ≠ zero) → (b ≠ zero) → (a * b ≠ zero) := by
  intro ha
  intro hb
  -- Goal : a * b ≠ zero
  -- ha   : a ≠ zero
  -- hb   : b ≠ zero
  cases a with
  | zero =>
    -- ha   : zero ≠ zero
    tauto
  | succ aa =>
    cases b with
    | zero =>
      -- hb   : zero ≠ zero
      tauto
    | succ bb =>
      -- Goal : succ aa * succ bb ≠ zero
      rw [succ_mul]
      -- Goal : aa * succ bb + succ bb ≠ zero
      rw [add_succ]
      -- Goal : succ (aa * succ bb + bb) ≠ zero
      symm
      -- Goal : zero ≠ succ (aa * succ bb + bb)
      apply zero_ne_succ
      -- Done






-- World     :   Advanced Multiplication World
-- Level 8   :   mul_eq_zero

theorem mul_eq_zero (a b : MyNat) : (a * b = zero) → (a = zero   ∨   b = zero) := by
  have h := mul_ne_zero a b
  tauto










-- The game tells me                 "induction b with d hd generalizing c"
-- ... but when I try it tells me:   "You have not unlocked the tactic 'generalizing' yet!"
-- :(

-- World     :   Advanced Multiplication World
-- Level 9   :   mul_left_cancel

theorem mul_left_cancel2 (a b c : MyNat) : (a * b = a * c) → (a ≠ zero) → b = c := by
  intro h
  intro ha
  -- h    : a * b = a * c
  -- ha   : a ≠ zero
  -- Goal : b = c
  induction b generalizing c with





  | zero =>
    --    h : a * zero = a * c
    -- Goal : zero = c
    cases c with
    | zero =>
      -- Goal : zero = zero
      rfl
    | succ cc =>
      -- h    : a * zero = a * succ cc
      -- Goal : zero = succ cc
      rw [mul_zero] at h
      -- h    : zero = a * succ cc
      symm at h
      -- h    : a * succ cc = zero
      apply mul_eq_zero at h
      -- h    : a = zero   ∨   succ cc = zero
      cases h with
      | inl hl =>
        -- hl   : a = zero
        apply ha at hl
        -- hl   : False
        tauto
      | inr hr =>
        -- hr   : succ cc = zero
        symm
        -- hr   : zero = succ cc
        exact hr





  | succ bb hb =>
    -- hb   : ∀ (c : MyNat), a * bb = a * c → bb = c
    -- Goal : succ bb = c
    cases c with
    | zero =>
      -- h    : a * succ bb = a * zero
      -- Goal : succ bb = zero
      rw [mul_zero] at h
      -- h    : a * succ bb = zero
      apply mul_eq_zero at h
      -- h    : a = zero ∨ succ bb = zero
      tauto
    | succ cc =>
      -- h    : a * succ bb = a * succ cc
      -- Goal : succ bb = succ cc
      repeat rw [mul_succ] at h
      -- h    : a * bb + a = a * cc + a
      apply add_right_cancel at h
      -- h    : a * bb = a * cc
      have hb_cc := hb cc
      -- hb_cc: a * bb = a * cc   →   bb = cc
      apply hb_cc at h
      -- h    : bb = cc
      rw [h]
      -- Done : succ cc = succ cc



-- I can't reach level 10 because of the bug :(
