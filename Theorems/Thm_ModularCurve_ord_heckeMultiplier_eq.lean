import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_ModularCurve_ord_heckeMultiplier_eq
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve KaehlerDifferential

theorem ModularCurve.ord_heckeMultiplier_eq
    (k : Type*) [Field k] [PerfectField k] (N ℓ : ℕ) [NeZero N] [NeZero ℓ] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (hα : (heckeAlphaC k N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC k N ℓ).toRingHom.IsIntegral)
    [Algebra.IsAlgebraic ↥(IntermediateField.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)]
    [FiniteDimensional ↥(IntermediateField.adjoin k ({heckeAlphaC k N ℓ (jGeomGen k N)} : Set ↥(charLDegeneracyRoof k N ℓ))) ↥(charLDegeneracyRoof k N ℓ)]
    (h : ↥(charLDegeneracyRoof k N ℓ))
    (hD : KaehlerDifferential.D k ↥(charLDegeneracyRoof k N ℓ) (heckeBetaC k N ℓ (jGeomGen k N))
          = h • pullbackDiff (heckeAlphaC k N ℓ) (KaehlerDifferential.D k ↥(modularFunctionFieldC k N) (jGeomGen k N)))
    (hDα : KaehlerDifferential.D k ↥(charLDegeneracyRoof k N ℓ) (heckeAlphaC k N ℓ (jGeomGen k N)) ≠ 0)
    (hDβ : KaehlerDifferential.D k ↥(charLDegeneracyRoof k N ℓ) (heckeBetaC k N ℓ (jGeomGen k N)) ≠ 0)
    (y : Place k ↥(charLDegeneracyRoof k N ℓ))
    (heα : ((Place.ramificationIndexAlong (heckeAlphaC k N ℓ) y : ℕ) : k) ≠ 0)
    (heβ : ((Place.ramificationIndexAlong (heckeBetaC k N ℓ) y : ℕ) : k) ≠ 0) :
    y.ord h
      = ((Place.ramificationIndexAlong (heckeBetaC k N ℓ) y : ℤ)
            * (y.restrictAlong (heckeBetaC k N ℓ) hβ).ordDiff
                (KaehlerDifferential.D k ↥(modularFunctionFieldC k N) (jGeomGen k N))
          + (Place.ramificationIndexAlong (heckeBetaC k N ℓ) y : ℤ))
        - ((Place.ramificationIndexAlong (heckeAlphaC k N ℓ) y : ℤ)
            * (y.restrictAlong (heckeAlphaC k N ℓ) hα).ordDiff
                (KaehlerDifferential.D k ↥(modularFunctionFieldC k N) (jGeomGen k N))
          + (Place.ramificationIndexAlong (heckeAlphaC k N ℓ) y : ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ord_heckeMultiplier_eq.solution
