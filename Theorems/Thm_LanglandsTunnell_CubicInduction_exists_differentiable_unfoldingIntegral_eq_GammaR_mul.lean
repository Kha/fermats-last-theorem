import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse

theorem LanglandsTunnell.CubicInduction.exists_differentiable_unfoldingIntegral_eq_GammaR_mul
    (u₃ : ℂ) (a₃ : ZMod 2)
    (P₂ : RealArchParam)
    (D : ArchDatumR P₂)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (ha : a ≠ 0)
    (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P₂.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P₂.twist 0 a).gammaC, -ν.re < c₀))
    (κ : ℝ)
    (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (t : ℂ) (e : ℤ) :
    ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
      (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
        ‖P s‖ ≤ C * Real.exp (A * |s.im|)) ∧
      ∀ s : ℂ, max c₀ (-(u₃).re) - t.re < s.re → D.zeta_abscissa < s.re + t.re →
        (κ : ℂ) *
          (ArchR.quasiChar (u₃ + 1) a₃ (StandardKernel.realMat gInf).det *
            ∫ x : Fin 2 → Fin 2 → ℝ,
              godementInner3 psiInf S (Matrix.of x) (StandardKernel.realMat gInf) *
                ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of x).det *
                  (((|(Matrix.of x).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                D.zetaEntire (ArchR.diagOne (a : ℝ) * (Matrix.of x)⁻¹) t (e : ZMod 2) s) =
          Complex.Gammaℝ (s + (u₃ + t + LanglandsTunnell.signShift (a₃ + (e : ZMod 2)))) * P s := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_unfoldingIntegral_eq_GammaR_mul.solution
