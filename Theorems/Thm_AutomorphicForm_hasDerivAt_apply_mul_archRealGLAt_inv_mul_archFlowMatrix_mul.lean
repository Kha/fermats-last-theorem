import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_hasDerivAt_apply_mul_archRealGLAt_inv_mul_archFlowMatrix_mul

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.InfinitePlace
open AutomorphicForm
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.hasDerivAt_apply_mul_archRealGLAt_inv_mul_archFlowMatrix_mul
    (K : Type) [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal)
    (G : AdelicGL2 (𝓞 K) K → ℂ) (hG : IsArchSmoothAt hw G) (y : AdelicGL2 (𝓞 K) K)
    (m : GL (Fin 2) ℝ) (d : ArchDir) :
    let Y : Matrix (Fin 2) (Fin 2) ℝ :=
      ((m⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * archDirMatrix d * (m : Matrix (Fin 2) (Fin 2) ℝ)
    HasDerivAt (fun s : ℝ => G (y * archRealGLAt hw (m⁻¹ * archFlowMatrix d s * m)))
      ((((Y 0 0 - Y 1 1) / 2 : ℝ) : ℂ) * archDerivAt hw ArchDir.H G y +
        ((Y 0 1 : ℝ) : ℂ) * archDerivAt hw ArchDir.E G y +
        ((Y 1 0 : ℝ) : ℂ) * archDerivAt hw ArchDir.Fm G y) 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_hasDerivAt_apply_mul_archRealGLAt_inv_mul_archFlowMatrix_mul.solution
