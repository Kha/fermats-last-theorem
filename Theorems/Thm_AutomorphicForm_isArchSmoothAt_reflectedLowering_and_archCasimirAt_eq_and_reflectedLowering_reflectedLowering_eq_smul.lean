import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isArchSmoothAt_reflectedLowering_and_archCasimirAt_eq_and_reflectedLowering_reflectedLowering_eq_smul

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem AutomorphicForm.isArchSmoothAt_reflectedLowering_and_archCasimirAt_eq_and_reflectedLowering_reflectedLowering_eq_smul
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (T : (AdelicGL2 (𝓞 F) F → ℂ) → AdelicGL2 (𝓞 F) F → ℂ)
    (hT : T = fun (θ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) =>
      (archDerivAt hw ArchDir.H θ - Complex.I • (archDerivAt hw ArchDir.E θ + archDerivAt hw ArchDir.Fm θ))
        (g * archRealGLAt hw UpperHalfPlane.J))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ) :
    (HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ →
        archDerivAt hw ArchDir.E φ - archDerivAt hw ArchDir.Fm φ = Complex.I • φ) ∧
      IsArchSmoothAt hw (T φ) ∧
      (HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ → HasArchCharacterAt₀ F w (archWeightCharAt hw 1) (T φ)) ∧
      (∀ lam : ℂ, archCasimirAt hw φ = lam • φ → archCasimirAt hw (T φ) = lam • T φ) ∧
      (∀ lam : ℂ, archCasimirAt hw φ = lam • φ → HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ →
        T (T φ) = (1 - 4 * lam) • φ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isArchSmoothAt_reflectedLowering_and_archCasimirAt_eq_and_reflectedLowering_reflectedLowering_eq_smul.solution
