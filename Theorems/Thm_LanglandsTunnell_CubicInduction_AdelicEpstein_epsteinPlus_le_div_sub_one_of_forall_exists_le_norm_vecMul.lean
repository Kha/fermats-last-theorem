import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_le_div_sub_one_of_forall_exists_le_norm_vecMul

set_option autoImplicit false

open NumberField MeasureTheory

theorem LanglandsTunnell.CubicInduction.AdelicEpstein.epsteinPlus_le_div_sub_one_of_forall_exists_le_norm_vecMul
    [MeasurableSpace (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)]
    (du : Measure (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ))
    (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (M R₀ r : ℝ) (hR₀ : 0 ≤ R₀) (hr : 0 < r)
    (hM : ∀ x, ‖Φ x‖ ≤ M)
    (hsupp : ∀ x, Φ x ≠ 0 → ∀ i, ‖(x i).1 Rat.infinitePlace‖ ≤ R₀)
    (L : AddSubgroup (Fin 3 → IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))
    (hL : ∀ x, Φ x ≠ 0 → (fun i => (x i).2) ∈ L)
    (hLu : ∀ (u : IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)
      (z : Fin 3 → IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ), z ∈ L →
        (fun i => ((u : (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) * z i) ∈ L)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hsep : ∀ ξ : Fin 3 → ℚ, ξ ≠ 0 →
      (fun i => (Matrix.vecMul (adelicDiag ξ) (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i).2) ∈ L →
        ∃ i, r ≤ ‖(Matrix.vecMul (adelicDiag ξ) (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i).1
          Rat.infinitePlace‖)
    (σ : ℝ) (hσ : 1 < σ) :
    epsteinPlus du Φ σ g ≤
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ *
          (9 * M * (R₀ / r) ^ (3 * σ) / (σ - 1))) * du Set.univ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_le_div_sub_one_of_forall_exists_le_norm_vecMul.solution
