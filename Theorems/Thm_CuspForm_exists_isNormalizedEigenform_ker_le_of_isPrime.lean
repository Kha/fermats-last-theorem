import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_CuspForm_exists_isNormalizedEigenform_ker_le_of_isPrime
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq

theorem CuspForm.exists_isNormalizedEigenform_ker_le_of_isPrime {N : ℕ} [NeZero N] (hN : CuspForm.HasIntegralStructure N 2) (𝔭 : Ideal (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N})) (h𝔭 : 𝔭.IsPrime) (hchar : ∀ n : ℤ, algebraMap ℤ (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) n ∈ 𝔭 → n = 0) : ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2), f.IsNormalizedEigenform ∧ ∀ t : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}, (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = 0 → t ∈ 𝔭 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_isNormalizedEigenform_ker_le_of_isPrime.solution
