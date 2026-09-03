import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import P2M.Util
import P2M.Sol.S_AutomorphicForm_fderiv_apply_mul_archComplexLiftAt_eq_of_isArchSmoothAtComplex

set_option autoImplicit false

open NumberField NumberField.InfinitePlace AutomorphicForm Complex

theorem AutomorphicForm.fderiv_apply_mul_archComplexLiftAt_eq_of_isArchSmoothAtComplex
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (g : AdelicGL2 (𝓞 F) F) (e : Fin 2 → Fin 2 → ℂ) (he : (Matrix.of e).det ≠ 0) (Y : Fin 2 → Fin 2 → ℂ) :
    fderiv ℝ (fun e' : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e')) e Y =
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 - ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).re *
          archDerivAtComplex hw ArchDirComplex.H φ (g * archComplexLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 - ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).im *
          archDerivAtComplex hw ArchDirComplex.iH φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 0 1).re * archDerivAtComplex hw ArchDirComplex.E φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 0 1).im * archDerivAtComplex hw ArchDirComplex.iE φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 1 0).re * archDerivAtComplex hw ArchDirComplex.Fm φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 1 0).im * archDerivAtComplex hw ArchDirComplex.iFm φ (g * archComplexLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 + ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).re *
          deriv (fun s : ℝ => φ (g * archComplexLiftAt hw e *
            archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom
              (Units.mk0 (Complex.exp (s : ℂ)) (Complex.exp_ne_zero _))))) 0 +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 + ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).im *
          deriv (fun s : ℝ => φ (g * archComplexLiftAt hw e *
            archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom
              (Units.mk0 (Complex.exp ((s : ℂ) * I)) (Complex.exp_ne_zero _))))) 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_fderiv_apply_mul_archComplexLiftAt_eq_of_isArchSmoothAtComplex.solution
