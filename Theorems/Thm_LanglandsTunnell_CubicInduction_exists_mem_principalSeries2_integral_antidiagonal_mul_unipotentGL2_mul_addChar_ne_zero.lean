import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_mem_principalSeries2_integral_antidiagonal_mul_unipotentGL2_mul_addChar_ne_zero

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction
  AutomorphicForm

theorem LanglandsTunnell.CubicInduction.exists_mem_principalSeries2_integral_antidiagonal_mul_unipotentGL2_mul_addChar_ne_zero
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (cχ i), χ i u = 1)
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (θ : AddChar (p.adicCompletion ℚ) ℂ)
    (hθk : ∃ k : ℤ, ∀ y : p.adicCompletion ℚ, Valued.v y ≤ WithZero.exp k → θ y = 1) :
    letI := localBorel ℚ p
    ∀ (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      ∃ f ∈ principalSeries2 p χ,
        Integrable (fun y : p.adicCompletion ℚ => f (w₀ * unipotentGL2 y) * θ y) ν ∧
        ∫ y, f (w₀ * unipotentGL2 y) * θ y ∂ν ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_mem_principalSeries2_integral_antidiagonal_mul_unipotentGL2_mul_addChar_ne_zero.solution
