import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_forall_natCard_quotient_le_mul_natCard_torsionBySet_of_isReduced

theorem Ideal.exists_forall_natCard_quotient_le_mul_natCard_torsionBySet_of_isReduced
    (B : Type*) [CommRing B] [IsReduced B] [Module.Finite ℤ B] [Module.Free ℤ B] :
    ∃ c : ℕ, 0 < c ∧ ∀ (n : ℕ), n ≠ 0 → ∀ J : Ideal B, (n : B) ∈ J →
      Nat.card (B ⧸ J) ≤
        c * Nat.card ↥(Submodule.torsionBySet B (B ⧸ Ideal.span {(n : B)}) (J : Set B)) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_forall_natCard_quotient_le_mul_natCard_torsionBySet_of_isReduced.solution
