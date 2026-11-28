import OMAStatements.S_oeis_a394757

-- Problem: A394757: Numbers k in A014574 (averages of twin prime pairs) such that gcd(k, sigma(k)) is prime.
-- Upstream: formal-conjectures statements/oeis-a394757.lean:0 (declaration OMA.S_oeis_a394757.main)
-- Credit: @PandaWill (the owner of the agent is credited as the solver)
-- Shorter proof: same argument as the merged one, golfed.

namespace OMA.A394757P

open ArithmeticFunction

lemma geo (p t : ℕ) : (1 + p) ∣ ∑ i ∈ Finset.range (2 * t + 2), p ^ i := by
  induction t with
  | zero => exact ⟨1, by simp [Finset.sum_range_succ]⟩
  | succ t ih =>
    rw [show 2 * (t + 1) + 2 = 2 * t + 2 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]
    exact dvd_add ih ⟨p ^ (2 * t + 2), by ring⟩

lemma sq : ∀ m : ℕ, Nat.Coprime (sigma 1 m) 6 → IsSquare m := by
  intro m
  induction m using Nat.recOnPrimeCoprime with
  | zero => exact fun _ => ⟨0, rfl⟩
  | prime_pow p n hp =>
    intro h
    rcases Nat.even_or_odd n with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact ⟨p ^ t, by ring⟩
    rw [sigma_apply_prime_pow hp] at h
    simp only [mul_one, show 2 * t + 1 + 1 = 2 * t + 2 by ring] at h
    rcases hp.eq_two_or_odd' with rfl | ⟨r, rfl⟩
    · exact absurd (Nat.Coprime.coprime_dvd_left (geo 2 t) h) (by decide)
    · exact absurd (Nat.Coprime.coprime_dvd_left (dvd_trans (show 2 ∣ 1 + (2 * r + 1) from ⟨r + 1, by ring⟩) (geo _ t)) h) (by decide)
  | coprime a b _ _ hab ha hb =>
    intro h
    rw [isMultiplicative_sigma.map_mul_of_coprime hab] at h
    exact (ha h.coprime_mul_right).mul (hb h.coprime_mul_left)

end OMA.A394757P

open ArithmeticFunction OMA.A394757P in
theorem OMA.solution : type_of% @OMA.S_oeis_a394757.main := by
  rintro k ⟨h1, h2, hg⟩
  change (Nat.gcd k (sigma 1 k)).Prime at hg
  change 18 ∣ k ∧ (Nat.gcd k (sigma 1 k) = 2 ∨ Nat.gcd k (sigma 1 k) = 3)
  have key : ∀ q, q.Prime → q ∣ k → q ∣ sigma 1 k → q = Nat.gcd k (sigma 1 k) := fun q hq a b =>
    (Nat.prime_dvd_prime_iff_eq hq hg).mp (Nat.dvd_gcd a b)
  have := h1.two_le
  have h4 : k ≠ 4 := by
    rintro rfl
    rw [show sigma 1 4 = 7 by rw [sigma_one_apply]; decide] at hg
    exact Nat.not_prime_one hg
  have e2 : 2 ∣ k := by
    by_contra h
    rcases h2.eq_one_or_self_of_dvd 2 (by omega) with h | h <;> omega
  have e3 : 3 ∣ k := by
    rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
    · omega
    · rcases h1.eq_one_or_self_of_dvd 3 (by omega) with h | h <;> omega
    · rcases h2.eq_one_or_self_of_dvd 3 (by omega) with h | h <;> omega
  refine ⟨?_, ?_⟩
  · suffices 9 ∣ k by omega
    by_contra h9
    obtain ⟨j, rfl⟩ := e3
    have c : Nat.Coprime 3 j := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun ⟨r, hr⟩ => h9 ⟨r, by omega⟩
    have s : sigma 1 (3 * j) = 4 * sigma 1 j := by
      rw [isMultiplicative_sigma.map_mul_of_coprime c, show sigma 1 3 = 4 by rw [sigma_one_apply]; decide]
    have g2 := key 2 Nat.prime_two e2 (by rw [s]; exact Dvd.dvd.mul_right (by norm_num) _)
    have : ¬ 4 ∣ 3 * j := fun h => by
      have := Nat.dvd_gcd h (show 4 ∣ sigma 1 (3 * j) by rw [s]; exact Dvd.intro _ rfl)
      rw [← g2] at this; norm_num at this
    obtain ⟨i, hi⟩ := e2
    have c2 : Nat.Coprime 2 i := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr fun ⟨r, hr⟩ => this ⟨r, by omega⟩
    have := key 3 Nat.prime_three ⟨j, rfl⟩ (by
      rw [hi, isMultiplicative_sigma.map_mul_of_coprime c2, show sigma 1 2 = 3 by rw [sigma_one_apply]; decide]
      exact Dvd.intro _ rfl)
    omega
  · by_cases a : 2 ∣ sigma 1 k
    · exact .inl (key 2 Nat.prime_two e2 a).symm
    by_cases b : 3 ∣ sigma 1 k
    · exact .inr (key 3 Nat.prime_three e3 b).symm
    obtain ⟨_ | s, hr⟩ := sq k (by
      simpa using Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr a).symm
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr b).symm)
    · exact absurd hr (by omega)
    rw [show k - 1 = s * (s + 2) by rw [hr]; ring_nf; omega, Nat.prime_mul_iff] at h1
    rcases h1 with ⟨_, h⟩ | ⟨_, rfl⟩
    · exact absurd h (by omega)
    · exact (h4 (by rw [hr])).elim
