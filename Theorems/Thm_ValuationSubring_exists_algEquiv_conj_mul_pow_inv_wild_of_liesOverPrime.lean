import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime
attribute [-instance] WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

theorem ValuationSubring.exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime {q : ℕ} (hq : q.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) : ∃ φ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), ∀ τ ∈ A.inertiaSubgroupIn ℚ, φ * τ * φ⁻¹ * (τ ^ q)⁻¹ ∈ A.inertiaSubgroupIn ℚ ∧ ∀ z : AlgebraicClosure ℚ, z ≠ 0 → (φ * τ * φ⁻¹ * (τ ^ q)⁻¹) z * z⁻¹ - 1 ∈ A.nonunits := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime.solution
