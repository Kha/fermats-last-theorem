import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_CubicInductionForm_twist_det_package
attribute [-simp] LanglandsTunnell.CubicInduction.fnTwist3_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicInduction.CubicInductionForm.twist_det_package
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (pins : AutomorphicForm.CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (F : CubicInductionForm K pins ψ ν)
    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (_hχinf : ∀ v : InfinitePlace ℚ, v.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ χA v 0 0) :

    (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.form x) (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.form x) g) ∧

    IsGL3PsiWhittakerFn ψ (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.whittaker x) ∧
    IsGL3PsiWhittakerFn ψ⁻¹ (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)⁻¹ * F.dualWhittaker x) ∧

    (∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      HasSum (fun i : MirabolicIndex ℚ => (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.whittaker x) (mirabolicTranslate i * g)) ((fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.form x) g)) ∧
    (∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      HasSum (fun i : MirabolicIndex ℚ => (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)⁻¹ * F.dualWhittaker x) (mirabolicTranslate i * g)) (dualForm (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.form x) g)) ∧

    (Continuous F.form → Continuous (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.form x)) ∧
    (Continuous F.whittaker → Continuous (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.whittaker x)) ∧
    (Continuous F.dualWhittaker → Continuous (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)⁻¹ * F.dualWhittaker x)) ∧

    (IsGaugeMajorised3 ℚ F.whittaker → IsGaugeMajorised3 ℚ (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.whittaker x)) ∧
    (IsGaugeMajorised3 ℚ F.dualWhittaker → IsGaugeMajorised3 ℚ (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)⁻¹ * F.dualWhittaker x)) ∧

    (∀ v : HeightOneSpectrum (𝓞 ℚ), IsGL3PsiWhittakerFn (psiLoc ψ v) (fun y : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * F.whittakerLoc v y)) ∧

    (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))),
      (∀ v, IsBadPlace K ν v → v ∈ T) →
      (∀ v, ¬ IsUnramifiedCharAt χA v → v ∈ T) →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.whittaker x) g =
        F.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g) *
          ∏ v ∈ T, (fun y : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * F.whittakerLoc v y) (componentAt3 (𝓞 ℚ) ℚ v g)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_CubicInductionForm_twist_det_package.solution
