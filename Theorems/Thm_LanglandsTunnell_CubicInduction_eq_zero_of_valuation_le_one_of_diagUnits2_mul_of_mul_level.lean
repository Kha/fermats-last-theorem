import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level
    (v : HeightOneSpectrum (𝓞 ℚ)) (b : ℕ) (μ₁ μ₂ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hμ₁ : ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, μ₁ u ≠ 1)
    (hμ₂ : ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, μ₂ u ≠ 1)
    (F₀ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hleft : ∀ (u₁ u₂ : (v.adicCompletion ℚ)ˣ) (k : GL (Fin 2) (v.adicCompletion ℚ)),
      (∀ i j, Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      (∀ i j, Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      Valued.v (u₁ : v.adicCompletion ℚ) = 1 → Valued.v (u₂ : v.adicCompletion ℚ) = 1 →
      F₀ (LanglandsTunnell.CubicInduction.diagUnits2 u₁ u₂ * k) =
        ((μ₁ u₁ : ℂˣ) : ℂ) * ((μ₂ u₂ : ℂˣ) : ℂ) * F₀ k)
    (hleftU : ∀ (x : v.adicCompletion ℚ) (k : GL (Fin 2) (v.adicCompletion ℚ)),
      (∀ i j, Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      (∀ i j, Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      Valued.v x ≤ 1 →
      F₀ (AutomorphicForm.unipotentGL2 x * k) = F₀ k)
    (hdiag : ∀ (k : GL (Fin 2) (v.adicCompletion ℚ)) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v (u : v.adicCompletion ℚ) = 1 → F₀ (k * LanglandsTunnell.CubicInduction.diagUnitGL2 u) = F₀ k)
    (hupper : ∀ (k : GL (Fin 2) (v.adicCompletion ℚ)) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) → F₀ (k * AutomorphicForm.unipotentGL2 s) = F₀ k)
    (hlower : ∀ (k : GL (Fin 2) (v.adicCompletion ℚ)) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      F₀ (k * Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : v.adicCompletion ℚ), 0; s, 1]
        (by simp [Matrix.det_fin_two_of])) = F₀ k)
    (k : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : ∀ i j, Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1)
    (hkinv : ∀ i j, Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) :
    F₀ k = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level.solution
