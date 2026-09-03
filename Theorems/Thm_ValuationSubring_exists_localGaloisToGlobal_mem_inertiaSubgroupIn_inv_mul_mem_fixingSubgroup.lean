import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_localGaloisToGlobal_mem_inertiaSubgroupIn_inv_mul_mem_fixingSubgroup
attribute [-instance] WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

theorem ValuationSubring.exists_localGaloisToGlobal_mem_inertiaSubgroupIn_inv_mul_mem_fixingSubgroup
    (p : ℕ) [Fact p.Prime]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ (padicPlace p).inertiaSubgroupIn ℚ)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] :
    ∃ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      localGaloisToGlobal p τ ∈ (padicPlace p).inertiaSubgroupIn ℚ ∧
        σ⁻¹ * localGaloisToGlobal p τ ∈ F.fixingSubgroup := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_localGaloisToGlobal_mem_inertiaSubgroupIn_inv_mul_mem_fixingSubgroup.solution
