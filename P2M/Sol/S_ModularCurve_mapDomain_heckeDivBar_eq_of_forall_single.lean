import Definitions.Def_ModularCurve_HeckeOperator
import P2M.Util
namespace P2MW.S_ModularCurve_mapDomain_heckeDivBar_eq_of_forall_single

open AlgebraicCurve ModularCurve

theorem solution {L : Type*} [Field L] [Algebra ℚ L] {N ℓ : ℕ} [NeZero N] [NeZero ℓ] (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ) [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))] {k F' : Type*} [Field k] [Field F'] [Algebra k F'] (sp : Place L (laurentBaseChange L (modularFunctionFieldFull N)) → Place k F') (E : Divisor k F' →+ Divisor k F') (hE : ∀ v : Place L (laurentBaseChange L (modularFunctionFieldFull N)), Finsupp.mapDomain sp (heckeDivBar hα hβ (Finsupp.single v 1)) = E (Finsupp.single (sp v) 1)) (D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))) :
    Finsupp.mapDomain sp (heckeDivBar hα hβ D) = E (Finsupp.mapDomain sp D) := by
  have key : (Finsupp.mapDomain.addMonoidHom sp).comp (heckeDivBar hα hβ) =
      E.comp (Finsupp.mapDomain.addMonoidHom sp) := by
    refine Finsupp.addHom_ext fun v n => ?_
    have hv : (Finsupp.single v n : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))) = n • Finsupp.single v 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hv, map_zsmul, map_zsmul]
    congr 1
    simpa only [AddMonoidHom.comp_apply, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]
      using hE v
  simpa only [AddMonoidHom.comp_apply, Finsupp.mapDomain.addMonoidHom_apply] using
    DFunLike.congr_fun key D
