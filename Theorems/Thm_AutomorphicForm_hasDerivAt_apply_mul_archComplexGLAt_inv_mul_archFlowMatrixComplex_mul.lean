import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_hasDerivAt_apply_mul_archComplexGLAt_inv_mul_archFlowMatrixComplex_mul

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.InfinitePlace
open AutomorphicForm
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel
open scoped ComplexConjugate

theorem AutomorphicForm.hasDerivAt_apply_mul_archComplexGLAt_inv_mul_archFlowMatrixComplex_mul
    (K : Type) [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsComplex)
    (G : AdelicGL2 (𝓞 K) K → ℂ) (hG : IsArchSmoothAtComplex hw G) (y : AdelicGL2 (𝓞 K) K)
    (m : GL (Fin 2) ℂ) (d : ArchDirComplex) :
    let X : Matrix (Fin 2) (Fin 2) ℂ := match d with
      | .H => !![1, 0; 0, -1] | .E => !![0, 1; 0, 0] | .Fm => !![0, 0; 1, 0]
      | .iH => !![Complex.I, 0; 0, -Complex.I] | .iE => !![0, Complex.I; 0, 0] | .iFm => !![0, 0; Complex.I, 0]
    let Y : Matrix (Fin 2) (Fin 2) ℂ := ((m⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * X * (m : Matrix (Fin 2) (Fin 2) ℂ)
    HasDerivAt (fun s : ℝ => G (y * archComplexGLAt hw (m⁻¹ * archFlowMatrixComplex d s * m)))
      ((((Y 0 0 - Y 1 1) / 2).re : ℂ) * archDerivAtComplex hw ArchDirComplex.H G y +
        (((Y 0 0 - Y 1 1) / 2).im : ℂ) * archDerivAtComplex hw ArchDirComplex.iH G y +
        ((Y 0 1).re : ℂ) * archDerivAtComplex hw ArchDirComplex.E G y +
        ((Y 0 1).im : ℂ) * archDerivAtComplex hw ArchDirComplex.iE G y +
        ((Y 1 0).re : ℂ) * archDerivAtComplex hw ArchDirComplex.Fm G y +
        ((Y 1 0).im : ℂ) * archDerivAtComplex hw ArchDirComplex.iFm G y) 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_hasDerivAt_apply_mul_archComplexGLAt_inv_mul_archFlowMatrixComplex_mul.solution
