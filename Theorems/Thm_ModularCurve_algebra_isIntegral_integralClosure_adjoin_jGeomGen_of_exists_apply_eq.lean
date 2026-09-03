import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import P2M.Util
import P2M.Sol.S_ModularCurve_algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.NodeLocalized

theorem ModularCurve.algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (hred : Function.Surjective red)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    {C : Type*} [CommRing C]
    (g : C →+* ↥((integralClosure ↥(Algebra.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)).toSubring))
    (hconst : ∀ a : ↥(coeffSubring A K), ∃ c, ((g c : ↥((integralClosure ↥(Algebra.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)).toSubring)) : ↥(modularFunctionFieldC k N))
      = algebraMap k ↥(modularFunctionFieldC k N) (NodeLocalized.redRestrict red K a))
    (hj : ∃ c, ∃ n : ℕ, 0 < n ∧ ((g c : ↥((integralClosure ↥(Algebra.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)).toSubring)) : ↥(modularFunctionFieldC k N)) = jGeomGen k N ^ n) :
    @Algebra.IsIntegral C ↥((integralClosure ↥(Algebra.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)).toSubring) _ _ g.toAlgebra := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq.solution
