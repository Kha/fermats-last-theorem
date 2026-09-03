import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq
attribute [-instance] instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete

open ExtCitation
theorem ExtCitation.LocalLevel.exists_level_frobenius_pow_dvd_and_apply_eq (q : Nat.Primes)
    (φ : primeLocalGaloisGroup q) (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q)
    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F₀]
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hqn : ¬ (q : ℕ) ∣ n)
    {ζ α : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ n) (hα : α ^ n = ((q : ℕ) : AlgebraicClosure ℚ)) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F₀ ≤ F ∧ FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧ ζ ∈ F ∧ α ∈ F ∧
      ∀ m : ℕ, φ ^ m ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)
                        ⊔ (F.fixingSubgroup).comap (primeLocalToGlobal q) →
        n * d ∣ m ∧ primeLocalToGlobal q (φ ^ m) α = α := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq.solution
