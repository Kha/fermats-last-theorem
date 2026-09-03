import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_eq_coefficientFn_principalSeries3_of_isCosetEigenfunction_of_norm_eq_one
attribute [-simp] LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_eq_coefficientFn_principalSeries3_of_isCosetEigenfunction_of_norm_eq_one
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (α : Fin 3 → ℂ) (hα : ∀ i, ‖α i‖ = 1) (W : LocalGL3 v → ℂ)
    (hU : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hT₁ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W
      (cNormQ v * (α 0 + α 1 + α 2)))
    (hT₂ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W
      (cNormQ v * (α 0 * α 1 + α 0 * α 2 + α 1 * α 2)))
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = α 0 * α 1 * α 2 * W g)
    (hψ : IsGL3PsiWhittakerFn ψv W) (hlev : LanglandsTunnell.TateLocal.addCharLevel ψv = 0) (hne : ψv ≠ 1) :
    ∃ χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ),
      (∀ i, IsLocallyConstant (χ i)) ∧
      (∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((χ i x : ℂˣ) : ℂ)‖ = 1) ∧
      (∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖(x : v.adicCompletion ℚ)‖ = 1 → χ i x = 1) ∧
      ∃ Λ : ↥(LanglandsTunnell.CubicInduction.principalSeries3 v χ) →ₗ[ℂ] ℂ,
        LanglandsTunnell.CubicInduction.IsWhittakerFunctional3 ψv Λ ∧
        ∃ f : ↥(LanglandsTunnell.CubicInduction.principalSeries3 v χ),
          W = LanglandsTunnell.CubicInduction.coefficientFn Λ f := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_coefficientFn_principalSeries3_of_isCosetEigenfunction_of_norm_eq_one.solution
