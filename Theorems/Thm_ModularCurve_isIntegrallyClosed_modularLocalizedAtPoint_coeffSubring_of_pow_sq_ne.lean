module

public import Mathlib
public import Definitions.Def_ModularCurve_NodeDescent
import P2M.Util
import P2M.Sol.S_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_pow_sq_ne

@[expose] public section
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq

set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized
theorem ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_pow_sq_ne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q] [DecidableEq k]
    (red : A →+* k) (a : k) (ha : a ^ (q ^ 2) ≠ a)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a) :
    IsIntegrallyClosed ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_pow_sq_ne.solution
