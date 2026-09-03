import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ExtCitation_exists_level_dvd_of_frobenius_pow_mem_inertia_sup

open ExtCitation
theorem ExtCitation.exists_level_dvd_of_frobenius_pow_mem_inertia_sup (q : Nat.Primes)
    (φ : primeLocalGaloisGroup q) (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q)
    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F₀] (n : ℕ) (hn : 0 < n) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F₀ ≤ F ∧ FiniteDimensional ℚ F ∧
      ∀ j : ℕ, φ ^ j ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)
                        ⊔ (F.fixingSubgroup).comap (primeLocalToGlobal q) → n ∣ j := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_exists_level_dvd_of_frobenius_pow_mem_inertia_sup.solution
