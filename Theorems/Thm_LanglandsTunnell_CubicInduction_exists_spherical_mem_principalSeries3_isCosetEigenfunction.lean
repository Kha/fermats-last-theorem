import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_spherical_mem_principalSeries3_isCosetEigenfunction

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_spherical_mem_principalSeries3_isCosetEigenfunction
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖(x : v.adicCompletion ℚ)‖ = 1 → χ i x = 1) :
    ∃ f : ↥(principalSeries3 v χ), (f : LocalGL3 v → ℂ) 1 = 1 ∧
      IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (f : LocalGL3 v → ℂ) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) (f : LocalGL3 v → ℂ)
        (cNormQ v * (((χ 0 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) + ((χ 1 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) + ((χ 2 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ))) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) (f : LocalGL3 v → ℂ)
        (cNormQ v * (((χ 0 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) * ((χ 1 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) + ((χ 0 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) * ((χ 2 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) + ((χ 1 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) * ((χ 2 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ))) ∧
      ∀ g : LocalGL3 v, (f : LocalGL3 v → ℂ) (centralGen v * g) =
        ((χ 0 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) * ((χ 1 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) * ((χ 2 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) * (f : LocalGL3 v → ℂ) g := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_spherical_mem_principalSeries3_isCosetEigenfunction.solution
