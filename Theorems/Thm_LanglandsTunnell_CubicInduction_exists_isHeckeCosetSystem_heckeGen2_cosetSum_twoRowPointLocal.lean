import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ reps : Fin (Ideal.absNorm v.asIdeal ^ 2 + Ideal.absNorm v.asIdeal + 1) → LocalGL3 v,
      HeckeIntegralSeam.IsHeckeCosetSystem (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) reps ∧
      ∀ (ψv : AddChar (v.adicCompletion ℚ) ℂ), (∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1) →
        ∀ W : LocalGL3 v → ℂ, IsGL3PsiWhittakerFn ψv W →
            ∀ k₁ k₂ : ℕ, k₂ ≤ k₁ →
              cosetSum reps W (twoRowPointLocal v k₁ k₂) =
                cNormQ v ^ 2 * W (twoRowPointLocal v (k₁ + 1) (k₂ + 1)) +
                cNormQ v * W (twoRowPointLocal v (k₁ + 1) k₂ * (centralGen v * (heckeGen2 v)⁻¹)) +
                W (twoRowPointLocal v k₁ (k₂ + 1) * (centralGen v * (heckeGen2 v)⁻¹)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal.solution
