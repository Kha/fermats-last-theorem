import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (b : ℕ)
    (hχ : ∀ i, ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, χ i u ≠ 1)
    (Ψ : LanglandsTunnell.CubicInduction.LocalGL3 v → ℂ)
    (hΨ : Ψ ∈ LanglandsTunnell.CubicInduction.principalSeries3 v χ)
    (hdiag : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v (u : v.adicCompletion ℚ) = 1 →
      Ψ (g * LanglandsTunnell.CubicInduction.iotaGL (LanglandsTunnell.CubicInduction.diagUnitGL2 u)) = Ψ g)
    (hupper : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Ψ (g * LanglandsTunnell.CubicInduction.upperUnipotent3 s 0 0) = Ψ g)
    (hlower : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Ψ (g * LanglandsTunnell.CubicInduction.lowerUnipotent21 s) = Ψ g)
    (m : ℕ)
    (hm : ∀ κ : LanglandsTunnell.CubicInduction.LocalGL3 v,
      (∀ i j, Valued.v ((κ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) →
      ∀ g : LanglandsTunnell.CubicInduction.LocalGL3 v, Ψ (g * κ) = Ψ g)
    (hmid : ∀ k' : GL (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, Valued.v ((k' : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      (∀ i j, Valued.v ((k'⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      ∀ y : v.adicCompletion ℚ,
        Ψ (LanglandsTunnell.CubicInduction.weylPrime3 * LanglandsTunnell.CubicInduction.radicalP21 ![0, y] *
          LanglandsTunnell.CubicInduction.iotaGL k') = 0)
    (k : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : ∀ i j, Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1)
    (hkinv : ∀ i j, Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) :
    (∀ Y : Fin 2 → v.adicCompletion ℚ, WithZero.exp (m : ℤ) ≤ max (Valued.v (Y 0)) (Valued.v (Y 1)) →
      Ψ (LanglandsTunnell.CubicInduction.longWeyl3 * LanglandsTunnell.CubicInduction.iotaGL k *
        LanglandsTunnell.CubicInduction.radicalP21 Y) = 0) ∧
    ∀ (c : ℕ) (S : Finset (v.adicCompletion ℚ)), m ≤ c →
      (∀ s ∈ S, Valued.v s ≤ WithZero.exp (c : ℤ)) →
      (∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp (c : ℤ) →
        ∃! s, s ∈ S ∧ Valued.v (y - s) ≤ WithZero.exp (-(m : ℤ))) →
      ∑ s ∈ S, ∑ s' ∈ S, Ψ (LanglandsTunnell.CubicInduction.longWeyl3 * LanglandsTunnell.CubicInduction.iotaGL k *
        LanglandsTunnell.CubicInduction.radicalP21 ![s, s']) = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level.solution
