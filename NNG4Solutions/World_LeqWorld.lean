import NNG4Solutions.Define_MyNat
import NNG4Solutions.World_Addition
import NNG4Solutions.World_AdvancedAddition



namespace MyNat

-- For natural numbers:
-- a ≤ b means:  there exists a natural number c such that b = a + c
def le (a b : MyNat) :=  ∃ (c : MyNat), b = a + c



-- Use the MyNat.le function when the ≤ operator is used on MyNat's
instance : LE MyNat := ⟨MyNat.le⟩
-- No idea what these weird brackets mean but it doesn't compile without them.




-- We can prove   a ≤ b   by finding a non-negative c such that   a + c = b



-- World     :   ≤ World
-- Level 1   :   le_refl

theorem le_refl (a : MyNat) : a ≤ a := by
  -- Goal : a ≤ a
  use zero
  -- Goal : a = a + zero
  rw [add_zero]
  -- Done : a = a



-- World     :   ≤ World
-- Level 2   :   zero_le

theorem zero_le (a : MyNat) : zero ≤ a := by
  -- Goal : zero ≤ a
  use a
  -- Goal : a = zero + a
  rw [zero_add]
  -- Done : a = a






-- World     :   ≤ World
-- Level 3   :   le_succ_self

theorem le_succ_self (a : MyNat) : a ≤ succ a := by
  use one
  -- Goal : succ a = a + one
  rw [succ_eq_add_one]
  -- Done : a + one = a + one



-- World     :   ≤ World
-- Level 4   :   le_trans

theorem le_trans (a b c : MyNat) : (a ≤ b) → (b ≤ c) → (a ≤ c) := by
  intro hab
  -- ab   : a ≤ b
  -- Goal : a ≤ c
  intro hbc
  -- bc   : b ≤ c
  cases hab with
  | intro x hx =>
    -- hx   : b = a + x
    cases hbc with
    | intro y hy =>
      -- hy   : c = b + y
      use (x + y)
      -- Goal : c = a + (x + y)
      rw [← add_assoc]
      -- Goal : c = a + x + y
      rw [← hx]
      -- Goal : c = b + y
      exact hy




-- World     :   ≤ World
-- Level 5   :   le_zero

theorem le_zero (a : MyNat) : (a ≤ zero) → (a = zero) := by
  intro h
  cases h with
  | intro x hx =>
    -- hx   : zero = a + x
    -- Goal : a = zero
    symm at hx
    -- hx   : a + x = zero
    apply add_right_eq_zero at hx
    -- hx   : a = zero
    exact hx




-- World     :   ≤ World
-- Level 6   :   le_antisymm

theorem le_antisymm (a b: MyNat) : (a ≤ b) → (b ≤ a) → (a = b) := by
  intro hx
  -- hx   : a ≤ b
  intro hy
  -- hy   : b ≤ a
  -- Goal : a = b
  cases hx with
  | intro xx hxx =>
    -- hxx  : b = a + xx
    cases hy with
    | intro yy hyy =>
      -- hyy  : a = b + yy
      rw [hxx]
      -- Goal : a = a + xx
      rw [hyy] at hxx
      -- hxx  : b = b + yy + xx
      rw [add_assoc] at hxx
      -- hxx  : b = b + (yy + xx)
      symm at hxx
      -- hxx  : b + (yy + xx) = b
      apply add_right_eq_self at hxx
      -- hxx  : yy + xx = zero
      apply add_left_eq_zero at hxx
      -- hxx  : xx = zero
      rw [hxx]
      -- Goal : a = a + zero
      rw [add_zero]
      -- Done : a = a




-- World     :   ≤ World
-- Level 7   :   Dealing with or

theorem or_comm_on_nat_eq (a aa b bb : MyNat) : ((a = aa) ∨ (b = bb)) → ((b = bb) ∨ (a = aa)) := by
  intro h
  cases h with
    | inl ha =>
      -- ha   : a = aa
      right
      -- Goal : a = aa
      exact ha
      -- Done
    | inr hb =>
      -- hb   : b = bb
      left
      -- Goal : b = bb
      exact hb

-- More generically:

theorem or_comm (a b : Prop) : (a ∨ b) → (b ∨ a) := by
  intro h
  cases h with
    | inl ha =>
      -- ha   : a
      right
      -- Goal : a
      exact ha
      -- Done
    | inr hb =>
      -- hb   : b
      left
      -- Goal : b
      exact hb







-- World     :   ≤ World
-- Level 8   :   le_total

theorem le_total (a b : MyNat) : (a ≤ b) ∨ (b ≤ a) := by
  induction b with
    | zero =>
      right
      exact zero_le a
    | succ bb hb =>
      -- hb   : a ≤ bb   ∨   bb ≤ a
      -- Goal : a ≤ succ bb   ∨   succ bb ≤ a
      cases hb with
      | inl h1 =>
        -- h1   : a ≤ bb
        left
        -- Goal : a ≤ succ bb
        cases h1 with
        | intro h1_1 h1_2 =>
          -- h1_2 : bb = a + h1_1
          use (succ h1_1)
          -- Goal : succ bb = a + succ h1_1
          rw [add_succ]
          -- Goal : succ bb = succ (a + h1_1)
          rw [h1_2]
          -- Done : succ (a + h1_1) = succ (a + h1_1)
      | inr h2 =>
        cases h2 with
        | intro h2_1 h2_2 =>
          induction h2_1 with
          | zero =>
            rw [add_zero] at h2_2
            left
            rw [h2_2]
            exact le_succ_self bb
          | succ h2_1_2 =>
            right
            rw [h2_2]
            rw [add_succ]
            use h2_1_2
            rw [succ_add]
-- :(








-- World     :   ≤ World
-- Level 9   :   succ_le_succ

theorem succ_le_succ (a b : MyNat) : (succ a ≤ succ b) → (a ≤ b) := by
  intro h
  cases h with
  | intro c hc =>
    -- hc   : succ b = succ a + c
    -- Goal : a ≤ b
    use c
    -- Goal : b = a + c
    rw [succ_add] at hc
    -- hc   : succ b = succ (a + c)
    apply succ_inj at hc
    -- hc   : b = a + c
    exact hc







-- World     :   ≤ World
-- Level 10  :   le_one

theorem le_one (a : MyNat) : (a ≤ one) → (a = zero ∨ a = one) := by
  intro h
  cases a with
  | zero =>
    -- h    : zero ≤ one
    -- Goal : zero = zero    ∨    zero = one
    left
    -- Goal : zero = zero
    rfl
    -- Done
  | succ xx =>
    -- h    : succ xx ≤ one
    -- Goal : succ xx = zero   ∨   succ xx = one
    rw [one_eq_succ_zero] at h
    -- h    : succ xx ≤ succ zero
    apply succ_le_succ at h
    -- h    : xx ≤ zero
    apply le_zero at h
    -- h    : xx = zero
    right
    -- Goal : succ xx = one
    rw [h]
    -- Goal : succ zero = one
    rw [one_eq_succ_zero]
    -- Done : succ zero = succ zero



-- World     :   ≤ World
-- Level 11  :   le_two

theorem le_two (x : MyNat) : (x ≤ two) → (x = zero ∨ x = one ∨ x = two) := by
  intro hx
  -- hx   : x ≤ two
  -- Goal : x = zero   ∨   x = one   ∨   x = two
  cases x with
  | zero =>
    -- Goal : zero = zero   ∨   zero = one   ∨   zero = two
    left
    -- Goal : zero = zero
    rfl
  | succ xx =>
    -- Goal : succ xx = zero   ∨   succ xx = one   ∨   succ xx = two
    -- hx   : succ xx ≤ two
    right
    -- Goal : succ xx = one   ∨   succ xx = two
    cases xx with
    | zero =>
      left
      -- Goal : succ zero = one
      rw [one_eq_succ_zero]
      -- Done : succ zero = succ zero
    | succ xxx =>
      right
      -- Goal : succ (succ xxx) = two
      rw [two_eq_succ_one, one_eq_succ_zero] at hx
      -- hx   : succ (succ xxx) ≤ succ (succ zero)
      repeat apply succ_le_succ at hx
      -- hx   : xxx ≤ zero
      apply le_zero at hx
      -- hx   : xxx = zero
      rw [hx]
      -- Goal : succ (succ zero) = two
      rw [two_eq_succ_one, one_eq_succ_zero]
      -- Done : succ (succ zero) = succ (succ zero)

















theorem add_le_add_right (a b c : MyNat) : (a + c ≤ b + c) → (a ≤ b) := by
  induction c with
  | zero =>
    repeat rw [add_zero]
    intro h
    exact h
  | succ cc hc =>
    repeat rw [add_succ]
    intro hh
    apply succ_le_succ at hh
    apply hc at hh
    exact hh

theorem add_le_add_left (a b c : MyNat) : (c + a ≤ c + b) → (a ≤ b) := by
  rw [add_comm c a]
  rw [add_comm c b]
  apply add_le_add_right

theorem succ_le_succ_reverse (a b : MyNat) : (a ≤ b) → (succ a ≤ succ b) := by
  intro h
  induction b with
  | zero =>
    apply le_zero at h
    rw [h]
    use zero
    rw [add_zero]
  | succ bb =>
    cases h with
    | intro c hc =>
      rw [hc]
      use c
      rw [succ_add]

theorem add_le_add_left_reverse (c a b : MyNat) : (a ≤ b) → (c + a ≤ c + b) := by
  intro h
  induction c with
  | zero =>
    repeat rw [zero_add]
    exact h
  | succ cc hc =>
    repeat rw [succ_add]
    apply succ_le_succ_reverse
    exact hc

theorem add_le_add_right_reverse (c a b : MyNat) : (a ≤ b) → (a + c ≤ b + c) := by
  rw [add_comm a c]
  rw [add_comm b c]
  exact add_le_add_left_reverse c a b

theorem le_self_add (a b : MyNat) : (a ≤ a + b) := by
  nth_rewrite 1 [← add_zero a]
  apply add_le_add_left_reverse
  apply zero_le

theorem le_add_self (a b : MyNat) : (a ≤ b + a) := by
  rw [add_comm]
  apply le_self_add
