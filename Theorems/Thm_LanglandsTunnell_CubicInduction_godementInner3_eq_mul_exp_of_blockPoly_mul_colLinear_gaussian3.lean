import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_godementInner3_eq_mul_exp_of_blockPoly_mul_colLinear_gaussian3

set_option autoImplicit false

p2m_open "NumberField AutomorphicForm LanglandsTunnell.Converse MeasureTheory LanglandsTunnell.CubicInduction~integral_colHarmonic_pow_mul_gaussian_mul_fourierChar_fin_two"

theorem LanglandsTunnell.CubicInduction.godementInner3_eq_mul_exp_of_blockPoly_mul_colLinear_gaussian3
    (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (p₀ p₁ : MvPolynomial (Fin 2 × Fin 2) ℂ)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
      (MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((M v.1 (Fin.castSucc v.2) : ℝ) : ℂ)) p₀ * ((M 0 2 : ℝ) : ℂ) +
        MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((M v.1 (Fin.castSucc v.2) : ℝ) : ℂ)) p₁ * ((M 1 2 : ℝ) : ℂ)) *
        gaussian3 M)
    (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0) :
    godementInner3 psiInf S (Matrix.of e) 1
      = (MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((e v.1 v.2 : ℝ) : ℂ)) p₀ * (((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) +
          MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((e v.1 v.2 : ℝ) : ℂ)) p₁ * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)) *
          (Real.exp (-(Real.pi * ∑ i : Fin 2, ∑ j : Fin 2, e i j ^ 2)) : ℂ) *
          (((|(Matrix.of e).det|)⁻¹ : ℝ) : ℂ) *
          (-Complex.I * (a : ℂ)) *
          (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_godementInner3_eq_mul_exp_of_blockPoly_mul_colLinear_gaussian3.solution
