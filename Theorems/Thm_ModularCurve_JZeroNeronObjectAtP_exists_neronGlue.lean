import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_exists_neronGlue
attribute [-instance] NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp
attribute [-simp] ModularCurve.coordOf_apply ModularCurve.coordOfEquiv_apply ModularCurve.diffChar_coe_apply ModularCurve.gramRangeBasisOf_coe ModularCurve.gramMatrixOf_apply

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_neronGlue
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) :
    ∃ (Nfull : Scheme.{0}) (gN : Nfull ⟶ shBase A) (LN : RelativeGroupLaw ↥(shRing A) gN),
      LN.IsCommutative ∧
      (Smooth gN ∧ IsSeparated gN ∧ LocallyOfFiniteType gN ∧ QuasiCompact gN) ∧
      Function.Surjective (genericFibreRestrict ↥(shRing A) ↥(invField A) gN (𝟙 (shBase A))) ∧
      ∃ (openImm : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.shStr O.g) gN)
        (specN : SchemeHomOver (shPt A) gN → componentGroup O.width),
        IsOpenImmersion openImm.1 ∧
        (∀ {T : Scheme.{0}} (s : T ⟶ shBase A)
          (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.shStr O.g)),
          NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.shStr).mul s x y) openImm =
            LN.mul s (NeronModelInfra.schemeHomOverComp x openImm) (NeronModelInfra.schemeHomOverComp y openImm)) ∧
        (∀ y : SchemeHomOver (barPt A ≫ shPt A) gN,
          ∃ x : JZero (N₀ * p), NeronModelInfra.schemeHomOverComp (Λ.shGenLift (O.pts x)) openImm = y) ∧
        (∀ s s' : SchemeHomOver (shPt A) gN, specN (LN.mul (shPt A) s s') = specN s + specN s') ∧
        Function.Surjective specN ∧
        (∀ s : SchemeHomOver (shPt A) gN,
          specN s = 0 ↔ ∃ s₀ : SchemeHomOver Λ.σA O.g, NeronModelInfra.schemeHomOverComp (Λ.shLift s₀) openImm = s) ∧
        (∀ (x : ↥(inertiaInvariants A (N₀ * p))) (s : SchemeHomOver (shPt A) gN),
          (NeronModelInfra.schemeHomOverComp (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))) openImm).1 = barPt A ≫ s.1 →
            O.comp x = specN s) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_neronGlue.solution
