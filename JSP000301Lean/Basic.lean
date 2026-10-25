import Mathlib

/-- A natural number is powerful when every prime divisor has square dividing it. -/
def Powerful (n : Nat) : Prop :=
  ∀ p : Nat, Nat.Prime p → p ∣ n → p * p ∣ n

theorem powerful_12167 : Powerful 12167 := by
  intro p hp hdiv
  have h23 : 12167 = 23 ^ 3 := by norm_num
  have hdiv23pow : p ∣ 23 ^ 3 := by
    rw [← h23]
    exact hdiv
  have hdiv23 : p ∣ 23 := hp.dvd_of_dvd_pow hdiv23pow
  have hle : p ≤ 23 := Nat.le_of_dvd (by norm_num) hdiv23
  have hge : 2 ≤ p := hp.two_le
  interval_cases p
  all_goals (norm_num at hdiv23; try norm_num)

theorem powerful_12168 : Powerful 12168 := by
  intro p hp hdiv
  have hfact : 12168 = 2 ^ 3 * 3 ^ 2 * 13 ^ 2 := by norm_num
  have hdivprod : p ∣ (2 ^ 3 * 3 ^ 2) * 13 ^ 2 := by
    rw [← hfact]
    exact hdiv
  have hcases : p = 2 ∨ p = 3 ∨ p = 13 := by
    rcases hp.dvd_mul.mp hdivprod with h23 | h13
    · rcases hp.dvd_mul.mp h23 with h2 | h3
      · have hdvd2 : p ∣ 2 := hp.dvd_of_dvd_pow h2
        have hle : p ≤ 2 := Nat.le_of_dvd (m := p) (n := 2) (by norm_num) hdvd2
        have hge : 2 ≤ p := hp.two_le
        have : p = 2 := by omega
        exact Or.inl this
      · have hdvd3 : p ∣ 3 := hp.dvd_of_dvd_pow h3
        have hle : p ≤ 3 := Nat.le_of_dvd (m := p) (n := 3) (by norm_num) hdvd3
        have hge : 2 ≤ p := hp.two_le
        have : p = 3 := by
          interval_cases p
          all_goals (norm_num at hdvd3; try norm_num)
        exact Or.inr (Or.inl this)
    · have hdvd13 : p ∣ 13 := hp.dvd_of_dvd_pow h13
      have hle : p ≤ 13 := Nat.le_of_dvd (m := p) (n := 13) (by norm_num) hdvd13
      have hge : 2 ≤ p := hp.two_le
      have : p = 13 := by
        interval_cases p
        all_goals (norm_num at hdvd13; try norm_num)
      exact Or.inr (Or.inr this)
  rcases hcases with h2 | h3 | h13
  · subst p
    norm_num
  · subst p
    norm_num
  · subst p
    norm_num

theorem not_square_of_between (n : Nat)
    (h₁ : 110 * 110 < n) (h₂ : n < 111 * 111) :
    ¬ ∃ k : Nat, k * k = n := by
  rintro ⟨k, hk⟩
  have hk' : (k : Int) * (k : Int) = (n : Int) := by exact_mod_cast hk
  have hk_sq : ((k : Int) ^ 2) = (n : Int) := by
    simpa [pow_two] using hk'
  have h₁sq : ((110 : Int) ^ 2) < (n : Int) := by
    exact_mod_cast (by simpa [pow_two] using h₁)
  have h₂sq : (n : Int) < ((111 : Int) ^ 2) := by
    exact_mod_cast (by simpa [pow_two] using h₂)
  have hpos : 0 ≤ (k : Int) := by exact_mod_cast Nat.zero_le k
  have hlow_sq : ((110 : Int) ^ 2) < ((k : Int) ^ 2) := by
    nlinarith [h₁sq, hk_sq]
  have hhigh_sq : ((k : Int) ^ 2) < ((111 : Int) ^ 2) := by
    nlinarith [h₂sq, hk_sq]
  have hlow : (110 : Int) < (k : Int) := by
    have h := (sq_lt_sq.mp hlow_sq)
    simpa [abs_of_nonneg (by norm_num : (0 : Int) ≤ 110), abs_of_nonneg hpos] using h
  have hhigh : (k : Int) < (111 : Int) := by
    have h := (sq_lt_sq.mp hhigh_sq)
    simpa [abs_of_nonneg (by norm_num : (0 : Int) ≤ 111), abs_of_nonneg hpos] using h
  omega

theorem not_square_12167 : ¬ ∃ k : Nat, k * k = 12167 := by
  apply not_square_of_between
  · norm_num
  · norm_num

theorem not_square_12168 : ¬ ∃ k : Nat, k * k = 12168 := by
  apply not_square_of_between
  · norm_num
  · norm_num

/-- The complete `JSP-000301` counterexample. -/
theorem JSP000301_counterexample :
    Powerful 12167 ∧
    Powerful 12168 ∧
    12167 + 1 = 12168 ∧
    ¬ (∃ k : Nat, k * k = 12167) ∧
    ¬ (∃ k : Nat, k * k = 12168) := by
  exact ⟨powerful_12167, powerful_12168, by norm_num, not_square_12167,
    not_square_12168⟩
