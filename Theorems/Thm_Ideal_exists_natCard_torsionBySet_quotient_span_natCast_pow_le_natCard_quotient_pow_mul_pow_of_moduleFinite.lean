import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_natCard_torsionBySet_quotient_span_natCast_pow_le_natCard_quotient_pow_mul_pow_of_moduleFinite

theorem Ideal.exists_natCard_torsionBySet_quotient_span_natCast_pow_le_natCard_quotient_pow_mul_pow_of_moduleFinite
    (R : Type*) [CommRing R] [Module.Finite ℤ R]
    (I : Ideal R) (q : ℕ) [Fact q.Prime] (hqI : (q : R) ∈ I) :
    ∃ C : ℕ, ∀ m : ℕ,
      Nat.card ↥(Submodule.torsionBySet R (R ⧸ Ideal.span {(q : R) ^ m}) (↑(I ^ m) : Set R)) ≤
        Nat.card (R ⧸ I ^ m) * q ^ C := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_natCard_torsionBySet_quotient_span_natCast_pow_le_natCard_quotient_pow_mul_pow_of_moduleFinite.solution
