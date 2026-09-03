import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_rigidDataPow_raw_eq_act_of_curve_eq_of_level_eq_of_pair_eq_one
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

theorem WeierstrassCurve.DrinfeldGlobal.rigidDataPow_raw_eq_act_of_curve_eq_of_level_eq_of_pair_eq_one
    (A : Type) [CommRing A] (ℓ M' q : ℕ)
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (T : Type) [CommRing T] [Algebra A T]
    (x x' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (C : WeierstrassCurve.VariableChange T)

    (hcurve : x'.curve = ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act C x).curve)
    (htuple : x'.level.1 = ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act C x).level.1)
    (hkatz : x'.level.2.1 = ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act C x).level.2.1)

    (hx : ∃ hΔ : IsUnit x.level.2.2.curve.Δ,
      x.level.2.2.P = (𝒢 T x.level.2.2.curve hΔ).one (𝟙 _) ∧ x.level.2.2.Q = (𝒢 T x.level.2.2.curve hΔ).one (𝟙 _))
    (hx' : ∃ hΔ : IsUnit x'.level.2.2.curve.Δ,
      x'.level.2.2.P = (𝒢 T x'.level.2.2.curve hΔ).one (𝟙 _) ∧ x'.level.2.2.Q = (𝒢 T x'.level.2.2.curve hΔ).one (𝟙 _)) :
    x' = (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act C x := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_rigidDataPow_raw_eq_act_of_curve_eq_of_level_eq_of_pair_eq_one.solution
