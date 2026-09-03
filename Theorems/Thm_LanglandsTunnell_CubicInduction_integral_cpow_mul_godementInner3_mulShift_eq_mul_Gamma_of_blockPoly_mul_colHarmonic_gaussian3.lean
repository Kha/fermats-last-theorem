import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_integral_cpow_mul_godementInner3_mulShift_eq_mul_Gamma_of_blockPoly_mul_colHarmonic_gaussian3

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.CubicInduction.integral_cpow_mul_godementInner3_mulShift_eq_mul_Gamma_of_blockPoly_mul_colHarmonic_gaussian3
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (p : MvPolynomial (Fin 2 × Fin 2) ℂ) (m : ℕ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((M v.1 (Fin.castSucc v.2) : ℝ) : ℂ)) p *
        (((M 0 2 : ℝ) : ℂ) + (ε : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ m * gaussian3 M)
    (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0)
    (w : ℂ) (hw : -1 < (w + m).re) :
    (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ w *
        godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)
      = MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((e v.1 v.2 : ℝ) : ℂ)) p *
          (Real.exp (-(Real.pi * ∑ i : Fin 2, ∑ j : Fin 2, e i j ^ 2)) : ℂ) *
          (((|(Matrix.of e).det|)⁻¹ : ℝ) : ℂ) *
          (-Complex.I * (a : ℂ)) ^ m *
          ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) + (ε : ℂ) * Complex.I * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)) ^ m *
          ((1 / 2 : ℂ) *
            ((Real.pi * (a : ℝ) ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2) : ℝ) : ℂ)
                ^ (-((w + m + 1) / 2)) *
            Complex.Gamma ((w + m + 1) / 2)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_integral_cpow_mul_godementInner3_mulShift_eq_mul_Gamma_of_blockPoly_mul_colHarmonic_gaussian3.solution
