import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ExtCitation_exists_frobenius_pow_inv_mul_mem_inertia_sup_level
attribute [-instance] instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete

open ExtCitation
theorem ExtCitation.exists_frobenius_pow_inv_mul_mem_inertia_sup_level (q : Nat.Primes)
    (φ : primeLocalGaloisGroup q) (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] (g : primeLocalGaloisGroup q) :
    ∃ n : ℕ, (φ ^ n)⁻¹ * g ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)
                        ⊔ (F.fixingSubgroup).comap (primeLocalToGlobal q) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_exists_frobenius_pow_inv_mul_mem_inertia_sup_level.solution
