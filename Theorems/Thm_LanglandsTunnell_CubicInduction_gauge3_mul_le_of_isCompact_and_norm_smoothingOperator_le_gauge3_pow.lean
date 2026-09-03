import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_gauge3_mul_le_of_isCompact_and_norm_smoothingOperator_le_gauge3_pow
attribute [-simp] LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.gauge3_mul_le_of_isCompact_and_norm_smoothingOperator_le_gauge3_pow :
    (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K →
      ∃ C : ℝ, ∀ k ∈ K, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, gauge3 ℚ (g * k) ≤ C * gauge3 ℚ g) ∧
    ∀ (N : ℕ) (f φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ‖f g‖ ≤ C * gauge3 ℚ g ^ N) → SlabL2.IsSmoothingKernel φ →
        ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ‖SlabL2.smoothingOperator φ f g‖ ≤ C * gauge3 ℚ g ^ N := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_gauge3_mul_le_of_isCompact_and_norm_smoothingOperator_le_gauge3_pow.solution
