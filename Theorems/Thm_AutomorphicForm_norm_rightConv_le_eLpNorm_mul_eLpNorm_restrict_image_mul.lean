import Mathlib
import Definitions.Def_AutomorphicForm_RightConvolution
import P2M.Util
import P2M.Sol.S_AutomorphicForm_norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul

set_option autoImplicit false
open NumberField NumberField.AdelicHaar AutomorphicForm MeasureTheory

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul
    (K : Type) [Field K] [NumberField K]
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hφ : Continuous φ) (hf : Continuous f)
    (hfs : HasCompactSupport f) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    ‖rightConv K φ f g‖ ≤
      (eLpNorm f 2 (adelicGLHaar (Fin 2) (𝓞 K) K)).toReal *
        (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict ((fun x => g * x) '' tsupport f))).toReal := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul.solution
