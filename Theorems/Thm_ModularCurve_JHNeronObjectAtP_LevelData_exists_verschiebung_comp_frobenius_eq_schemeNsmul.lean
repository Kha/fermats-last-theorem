import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_JacJ1Iface
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_verschiebung_comp_frobenius_eq_schemeNsmul
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing
  ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.LevelData.exists_verschiebung_comp_frobenius_eq_schemeNsmul
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)

    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (σp : Spec (CommRingCat.of (ZMod p)) ⟶ base p)
    (F : SchemeHomOver (RelativeGroupLaw.baseChangeStr σp Λ.f) (RelativeGroupLaw.baseChangeStr σp Λ.f))
    (hF : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p]
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) (RelativeGroupLaw.baseChangeStr σp Λ.f)),
      (schemeHomOverComp x F).1 = Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x.1) :
    ∃ V : SchemeHomOver (RelativeGroupLaw.baseChangeStr σp Λ.f) (RelativeGroupLaw.baseChangeStr σp Λ.f),
      V.1 ≫ F.1 = (Λ.L.baseChange σp).schemeNsmul p ∧ F.1 ≫ V.1 = (Λ.L.baseChange σp).schemeNsmul p ∧

      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ZMod p)))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp Λ.f)),
        schemeHomOverComp ((Λ.L.baseChange σp).mul s x y) V =
          (Λ.L.baseChange σp).mul s (schemeHomOverComp x V) (schemeHomOverComp y V)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_verschiebung_comp_frobenius_eq_schemeNsmul.solution
