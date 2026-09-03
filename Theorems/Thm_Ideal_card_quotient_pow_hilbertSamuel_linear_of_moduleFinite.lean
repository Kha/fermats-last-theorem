import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_card_quotient_pow_hilbertSamuel_linear_of_moduleFinite

theorem Ideal.card_quotient_pow_hilbertSamuel_linear_of_moduleFinite
    (R : Type*) [CommRing R] [Module.Finite ℤ R]
    (I : Ideal R) (q : ℕ) [Fact q.Prime] (hqI : (q : R) ∈ I) :
    ∃ e C : ℕ, ∀ m : ℕ,
      Nat.card (R ⧸ I ^ m) ≤ q ^ (m * e + C) ∧
        q ^ (m * e) ≤ Nat.card (R ⧸ I ^ m) * q ^ C := by p2m_exact_reverting @_root_.P2MW.S_Ideal_card_quotient_pow_hilbertSamuel_linear_of_moduleFinite.solution
