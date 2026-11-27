import OMAStatements.S_oeis_a394757

-- Problem: A394757: Numbers k in A014574 (averages of twin prime pairs) such that gcd(k, sigma(k)) is prime.
-- Upstream: formal-conjectures statements/oeis-a394757.lean:0 (declaration OMA.S_oeis_a394757.main)
-- Credit: @PandaWill (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open ArithmeticFunction OMA.S_oeis_a394757

/-- `1 + p` divides `1 + p + ... + p ^ (2t+1)`. -/
lemma A394757D (p t : ℕ) : 1 + p ∣ ∑ i ∈ Finset.range (2 * t + 1 + 1), p ^ i := by
  induction t with
  | zero => simp [Finset.sum_range_succ]
  | succ t ih =>
    rw [show 2 * (t + 1) + 1 + 1 = 2 * t + 1 + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, add_assoc]
    exact dvd_add ih ⟨p ^ (2 * t + 2), by ring⟩

/-- If `σ m` is coprime to `6`, then `m` is a perfect square. -/
lemma A394757S (m : ℕ) : Nat.Coprime (sigma 1 m) 6 → IsSquare m := by
  induction m using Nat.recOnPrimeCoprime with
  | zero => exact fun _ => ⟨0, rfl⟩
  | prime_pow p n hp =>
    intro h
    rcases Nat.even_or_odd n with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact ⟨_, pow_add _ _ _⟩
    rw [sigma_one_apply_prime_pow hp] at h
    have := h.coprime_dvd_left (A394757D p t)
    rcases hp.eq_two_or_odd' with rfl | ⟨r, rfl⟩
    · exact absurd this (by decide)
    · exact absurd (this.coprime_dvd_left (by omega : 2 ∣ _)) (by decide)
  | coprime a b _ _ hab ha hb =>
    intro h
    rw [isMultiplicative_sigma.map_mul_of_coprime hab] at h
    exact (ha h.coprime_mul_right).mul (hb h.coprime_mul_left)

/-- If `p` divides `p * j` exactly once, then `p + 1` divides `σ (p * j)`. -/
lemma A394757X {p j : ℕ} (hp : p.Prime) (h : ¬ p ∣ j) : p + 1 ∣ sigma 1 (p * j) := by
  rw [isMultiplicative_sigma.map_mul_of_coprime (hp.coprime_iff_not_dvd.2 h), ← pow_one p,
    sigma_one_apply_prime_pow hp]
  exact Dvd.dvd.mul_right (by simp [Finset.sum_range_succ, add_comm]) _

theorem OMA.solution : type_of% @OMA.S_oeis_a394757.main := by
  rintro k ⟨h1, h2, hg⟩
  have hk4 : k ≠ 4 := by rintro rfl; exact absurd hg (by decide)
  set g := divisorGcd k
  -- a prime dividing both `k` and `σ k` is `g`
  have key : ∀ q, q.Prime → q ∣ k → q ∣ sigma 1 k → q = g := fun q hq a b =>
    (Nat.prime_dvd_prime_iff_eq hq hg).1 (Nat.dvd_gcd a b)
  have := h1.two_le
  have := h1.eq_one_or_self_of_dvd 3
  have := h2.eq_one_or_self_of_dvd 3
  have hk3 : 3 ∣ k := by omega
  have := h2.eq_one_or_self_of_dvd 2
  have hk2 : 2 ∣ k := by omega
  -- `9` divides `k`: otherwise `4 ∣ σ k`, so `g = 2`, so `2 ∥ k`, so `3 ∣ σ k` and `g = 3`
  have hk9 : 9 ∣ k := by
    by_contra h9
    have e := A394757X Nat.prime_three (by omega : ¬ 3 ∣ k / 3)
    rw [Nat.mul_div_cancel' hk3] at e
    have := key 2 Nat.prime_two hk2 (dvd_trans ⟨2, rfl⟩ e)
    have h4 : ¬ 4 ∣ k := fun h => by have : 4 ∣ g := Nat.dvd_gcd h e; omega
    have f := A394757X Nat.prime_two (by omega : ¬ 2 ∣ k / 2)
    rw [Nat.mul_div_cancel' hk2] at f
    have := key 3 Nat.prime_three hk3 f
    omega
  refine ⟨by omega, ?_⟩
  by_cases a : 2 ∣ sigma 1 k
  · exact .inl (key 2 Nat.prime_two hk2 a).symm
  by_cases b : 3 ∣ sigma 1 k
  · exact .inr (key 3 Nat.prime_three hk3 b).symm
  exfalso
  -- otherwise `k = r * r`, and `k - 1 = (r + 1) * (r - 1)` is not prime
  obtain ⟨r, rfl⟩ := A394757S k
    ((Nat.prime_two.coprime_iff_not_dvd.2 a).symm.mul_right (Nat.prime_three.coprime_iff_not_dvd.2 b).symm)
  rw [show r * r - 1 = (r + 1) * (r - 1) from Nat.mul_self_sub_mul_self_eq r 1, Nat.prime_mul_iff] at h1
  rcases h1 with ⟨-, h⟩ | ⟨p, h⟩
  · exact hk4 (by rw [show r = 2 by omega])
  · exact Nat.not_prime_zero (by rwa [show r = 0 by omega] at p)
