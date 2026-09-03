import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn
attribute [-instance] WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

theorem ValuationSubring.exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn
    (A : ValuationSubring (AlgebraicClosure ℚ))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    (∀ z : AlgebraicClosure ℚ, z ≠ 0 →
      ∃ a : (↥A)ˣ, ((a : ↥A) : AlgebraicClosure ℚ) * z = σ z ∧
        IsLocalRing.residue (↥A) (a : ↥A) = A.tameCharacter z σ) ∧
    ∀ u : (↥A)ˣ, A.tameCharacter ((u : ↥A) : AlgebraicClosure ℚ) σ = 1 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn.solution
