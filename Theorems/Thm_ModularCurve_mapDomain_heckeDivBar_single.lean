import Definitions.Def_ModularCurve_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_mapDomain_heckeDivBar_single

open AlgebraicCurve ModularCurve
theorem ModularCurve.mapDomain_heckeDivBar_single {L : Type*} [Field L] [Algebra ℚ L] {N ℓ : ℕ} [NeZero N] [NeZero ℓ] (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ) [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))] {k F' : Type*} [Field k] [Field F'] [Algebra k F'] (sp : Place L (laurentBaseChange L (modularFunctionFieldFull N)) → Place k F') (v : Place L (laurentBaseChange L (modularFunctionFieldFull N))) (n : ℤ) :
    Finsupp.mapDomain sp (heckeDivBar hα hβ (Finsupp.single v n)) = ∑ W ∈ Place.fiberAlong (heckeBetaBar L N ℓ) hβ v, Finsupp.single (sp (W.restrictAlong (heckeAlphaBar L N ℓ) hα)) (n * (W.ramificationIndexAlong (heckeBetaBar L N ℓ) : ℤ) * (W.inertiaDegAlong (heckeAlphaBar L N ℓ) hα : ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mapDomain_heckeDivBar_single.solution
