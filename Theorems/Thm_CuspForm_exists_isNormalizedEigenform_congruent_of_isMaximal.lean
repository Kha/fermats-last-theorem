import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_CuspForm_exists_isNormalizedEigenform_congruent_of_isMaximal
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq

theorem CuspForm.exists_isNormalizedEigenform_congruent_of_isMaximal {N : ℕ} [NeZero N] (hN : CuspForm.HasIntegralStructure N 2) (𝔪₁ : Ideal (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N})) (h𝔪₁ : 𝔪₁.IsMaximal) {p : ℕ} (hp𝔪 : (p : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁) : ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (_ : f.IsNormalizedEigenform) (𝔪' : Ideal (integralClosure ℤ ℂ)), 𝔪'.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪' ∧ ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (b : ℤ), CuspForm.heckeAlgebra.T hℓ hℓN hℓN - (b : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁ → ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧ a - (b : integralClosure ℤ ℂ) ∈ 𝔪' := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_isNormalizedEigenform_congruent_of_isMaximal.solution
