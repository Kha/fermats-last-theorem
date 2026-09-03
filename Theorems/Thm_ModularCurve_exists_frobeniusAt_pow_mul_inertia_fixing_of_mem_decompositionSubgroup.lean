import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.FieldTheory.Galois.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_frobeniusAt_pow_mul_inertia_fixing_of_mem_decompositionSubgroup
attribute [-instance] AlgebraicClosure.Rat.isGalois
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false

theorem ModularCurve.exists_frobeniusAt_pow_mul_inertia_fixing_of_mem_decompositionSubgroup (q : ℕ) (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ)
    (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L₀] :
    ∃ (n : ℕ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      τ ∈ A.inertiaSubgroupIn ℚ ∧ (φ ^ n * τ)⁻¹ * σ ∈ L₀.fixingSubgroup := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_frobeniusAt_pow_mul_inertia_fixing_of_mem_decompositionSubgroup.solution
