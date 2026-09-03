import Definitions.Def_ModularCurve_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_mapDomain_heckeDivBar_eq_of_forall_single

open AlgebraicCurve ModularCurve
theorem ModularCurve.mapDomain_heckeDivBar_eq_of_forall_single {L : Type*} [Field L] [Algebra ℚ L] {N ℓ : ℕ} [NeZero N] [NeZero ℓ] (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ) [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))] {k F' : Type*} [Field k] [Field F'] [Algebra k F'] (sp : Place L (laurentBaseChange L (modularFunctionFieldFull N)) → Place k F') (E : Divisor k F' →+ Divisor k F') (hE : ∀ v : Place L (laurentBaseChange L (modularFunctionFieldFull N)), Finsupp.mapDomain sp (heckeDivBar hα hβ (Finsupp.single v 1)) = E (Finsupp.single (sp v) 1)) (D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))) :
    Finsupp.mapDomain sp (heckeDivBar hα hβ D) = E (Finsupp.mapDomain sp D) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mapDomain_heckeDivBar_eq_of_forall_single.solution
