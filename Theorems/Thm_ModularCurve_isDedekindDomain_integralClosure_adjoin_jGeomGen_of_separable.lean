import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_SpecializationMap
import P2M.Util
import P2M.Sol.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable
    (k : Type*) [Field k] (N : ℕ) [NeZero N] (dataN : ModularPolynomialData N)
    (hsep : ((dataN.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    FiniteDimensional ↥(IntermediateField.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N) ∧
    Algebra.IsSeparable ↥(IntermediateField.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N) ∧
    IsDedekindDomain ↥(integralClosure ↥(Algebra.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)) ∧
    IsFractionRing ↥(integralClosure ↥(Algebra.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)) ↥(modularFunctionFieldC k N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.solution
