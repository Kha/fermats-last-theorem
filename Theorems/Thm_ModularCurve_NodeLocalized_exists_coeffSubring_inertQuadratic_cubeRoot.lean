import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import P2M.Util
import P2M.Sol.S_ModularCurve_NodeLocalized_exists_coeffSubring_inertQuadratic_cubeRoot
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized

theorem ModularCurve.NodeLocalized.exists_coeffSubring_inertQuadratic_cubeRoot
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (hirr : ∀ c : ↥(coeffSubring A K), redRestrict red K (c ^ 2 + c + 1) ≠ 0) :
    ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K')
      (hle : coeffSubring A K ≤ coeffSubring A K') (ζ : ↥(coeffSubring A K')),
      ζ ^ 2 + ζ + 1 = 0 ∧
      (∀ c : ↥(coeffSubring A K'), ∃ c₀ c₁ : ↥(coeffSubring A K),
        c = Subring.inclusion hle c₀ + ζ * Subring.inclusion hle c₁) ∧
      (∀ c : ↥(coeffSubring A K'), redRestrict red K' c = 0 ↔ ∃ d, c = Subring.inclusion hle ϖ * d) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_NodeLocalized_exists_coeffSubring_inertQuadratic_cubeRoot.solution
