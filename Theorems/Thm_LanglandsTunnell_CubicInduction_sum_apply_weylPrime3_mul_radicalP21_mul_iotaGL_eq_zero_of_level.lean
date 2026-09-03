import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_sum_apply_weylPrime3_mul_radicalP21_mul_iotaGL_eq_zero_of_level

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.sum_apply_weylPrime3_mul_radicalP21_mul_iotaGL_eq_zero_of_level
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (b : ℕ)
    (hχ : ∀ i, ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, χ i u ≠ 1)
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
    (m : ℕ)
    (hm : ∀ κ : LanglandsTunnell.CubicInduction.LocalGL3 v,
      (∀ i j, Valued.v ((κ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) →
      ∀ g : LanglandsTunnell.CubicInduction.LocalGL3 v, Φ (g * κ) = Φ g)
    (k : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : ∀ i j, Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1)
    (hkinv : ∀ i j, Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) :
    (∀ y : v.adicCompletion ℚ, WithZero.exp (m : ℤ) ≤ Valued.v y →
      Φ (LanglandsTunnell.CubicInduction.weylPrime3 * LanglandsTunnell.CubicInduction.radicalP21 ![0, y] *
        LanglandsTunnell.CubicInduction.iotaGL k) = 0) ∧
    ∀ (c : ℕ) (S : Finset (v.adicCompletion ℚ)), m ≤ c →
      (∀ s ∈ S, Valued.v s ≤ WithZero.exp (c : ℤ)) →
      (∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp (c : ℤ) →
        ∃! s, s ∈ S ∧ Valued.v (y - s) ≤ WithZero.exp (-(m : ℤ))) →
      ∑ s ∈ S, Φ (LanglandsTunnell.CubicInduction.weylPrime3 * LanglandsTunnell.CubicInduction.radicalP21 ![0, s] *
        LanglandsTunnell.CubicInduction.iotaGL k) = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_sum_apply_weylPrime3_mul_radicalP21_mul_iotaGL_eq_zero_of_level.solution
