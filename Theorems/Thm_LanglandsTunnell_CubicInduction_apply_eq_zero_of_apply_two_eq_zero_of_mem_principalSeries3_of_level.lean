import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (b : ℕ)
    (hχ₀ : ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, χ 0 u ≠ 1)
    (hχ₁ : ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, χ 1 u ≠ 1)
    (Φ : LanglandsTunnell.CubicInduction.LocalGL3 v → ℂ)
    (hΦ : Φ ∈ LanglandsTunnell.CubicInduction.principalSeries3 v χ)
    (hdiag : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v (u : v.adicCompletion ℚ) = 1 →
      Φ (g * LanglandsTunnell.CubicInduction.iotaGL (LanglandsTunnell.CubicInduction.diagUnitGL2 u)) = Φ g)
    (hupper : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Φ (g * LanglandsTunnell.CubicInduction.upperUnipotent3 s 0 0) = Φ g)
    (hlower : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Φ (g * LanglandsTunnell.CubicInduction.lowerUnipotent21 s) = Φ g)
    (x : LanglandsTunnell.CubicInduction.LocalGL3 v)
    (h20 : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (h21 : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0) :
    Φ x = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level.solution
