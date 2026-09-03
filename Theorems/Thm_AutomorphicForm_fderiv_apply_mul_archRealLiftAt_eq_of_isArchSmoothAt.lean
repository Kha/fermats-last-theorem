import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import P2M.Util
import P2M.Sol.S_AutomorphicForm_fderiv_apply_mul_archRealLiftAt_eq_of_isArchSmoothAt

set_option autoImplicit false

open NumberField NumberField.InfinitePlace AutomorphicForm

theorem AutomorphicForm.fderiv_apply_mul_archRealLiftAt_eq_of_isArchSmoothAt
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ)
    (g : AdelicGL2 (𝓞 F) F) (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0) (Y : Fin 2 → Fin 2 → ℝ) :
    fderiv ℝ (fun e' : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e')) e Y =
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 - ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2 : ℝ) *
          archDerivAt hw ArchDir.H φ (g * archRealLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 1 : ℝ) : ℂ) * archDerivAt hw ArchDir.E φ (g * archRealLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 1 0 : ℝ) : ℂ) * archDerivAt hw ArchDir.Fm φ (g * archRealLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 + ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2 : ℝ) *
          deriv (fun s : ℝ => φ (g * archRealLiftAt hw e *
            archRealGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom
              (Units.mk0 (Real.exp s) (Real.exp_ne_zero s))))) 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_fderiv_apply_mul_archRealLiftAt_eq_of_isArchSmoothAt.solution
