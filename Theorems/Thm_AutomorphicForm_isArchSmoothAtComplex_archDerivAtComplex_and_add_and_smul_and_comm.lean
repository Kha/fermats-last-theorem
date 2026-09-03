import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isArchSmoothAtComplex_archDerivAtComplex_and_add_and_smul_and_comm

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.isArchSmoothAtComplex_archDerivAtComplex_and_add_and_smul_and_comm
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex) :
    (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsArchSmoothAtComplex hw φ →
      ∀ d : ArchDirComplex, IsArchSmoothAtComplex hw (archDerivAtComplex hw d φ)) ∧
    (∀ φ ψ : AdelicGL2 (𝓞 F) F → ℂ, IsArchSmoothAtComplex hw φ → IsArchSmoothAtComplex hw ψ →
      ∀ d : ArchDirComplex,
        archDerivAtComplex hw d (φ + ψ) = archDerivAtComplex hw d φ + archDerivAtComplex hw d ψ) ∧
    (∀ (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (d : ArchDirComplex),
      archDerivAtComplex hw d (c • φ) = c • archDerivAtComplex hw d φ) ∧
    (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsArchSmoothAtComplex hw φ →
      (archDerivAtComplex hw .H (archDerivAtComplex hw .E φ)
          - archDerivAtComplex hw .E (archDerivAtComplex hw .H φ) = (2 : ℂ) • archDerivAtComplex hw .E φ) ∧
      (archDerivAtComplex hw .H (archDerivAtComplex hw .Fm φ)
          - archDerivAtComplex hw .Fm (archDerivAtComplex hw .H φ) = -((2 : ℂ) • archDerivAtComplex hw .Fm φ)) ∧
      (archDerivAtComplex hw .E (archDerivAtComplex hw .Fm φ)
          - archDerivAtComplex hw .Fm (archDerivAtComplex hw .E φ) = archDerivAtComplex hw .H φ) ∧
      (archDerivAtComplex hw .H (archDerivAtComplex hw .iH φ)
          - archDerivAtComplex hw .iH (archDerivAtComplex hw .H φ) = 0) ∧
      (archDerivAtComplex hw .H (archDerivAtComplex hw .iE φ)
          - archDerivAtComplex hw .iE (archDerivAtComplex hw .H φ) = (2 : ℂ) • archDerivAtComplex hw .iE φ) ∧
      (archDerivAtComplex hw .H (archDerivAtComplex hw .iFm φ)
          - archDerivAtComplex hw .iFm (archDerivAtComplex hw .H φ) = -((2 : ℂ) • archDerivAtComplex hw .iFm φ)) ∧
      (archDerivAtComplex hw .E (archDerivAtComplex hw .iH φ)
          - archDerivAtComplex hw .iH (archDerivAtComplex hw .E φ) = -((2 : ℂ) • archDerivAtComplex hw .iE φ)) ∧
      (archDerivAtComplex hw .E (archDerivAtComplex hw .iE φ)
          - archDerivAtComplex hw .iE (archDerivAtComplex hw .E φ) = 0) ∧
      (archDerivAtComplex hw .E (archDerivAtComplex hw .iFm φ)
          - archDerivAtComplex hw .iFm (archDerivAtComplex hw .E φ) = archDerivAtComplex hw .iH φ) ∧
      (archDerivAtComplex hw .Fm (archDerivAtComplex hw .iH φ)
          - archDerivAtComplex hw .iH (archDerivAtComplex hw .Fm φ) = (2 : ℂ) • archDerivAtComplex hw .iFm φ) ∧
      (archDerivAtComplex hw .Fm (archDerivAtComplex hw .iE φ)
          - archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm φ) = -archDerivAtComplex hw .iH φ) ∧
      (archDerivAtComplex hw .Fm (archDerivAtComplex hw .iFm φ)
          - archDerivAtComplex hw .iFm (archDerivAtComplex hw .Fm φ) = 0) ∧
      (archDerivAtComplex hw .iH (archDerivAtComplex hw .iE φ)
          - archDerivAtComplex hw .iE (archDerivAtComplex hw .iH φ) = -((2 : ℂ) • archDerivAtComplex hw .E φ)) ∧
      (archDerivAtComplex hw .iH (archDerivAtComplex hw .iFm φ)
          - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iH φ) = (2 : ℂ) • archDerivAtComplex hw .Fm φ) ∧
      (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ)
          - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iE φ) = -archDerivAtComplex hw .H φ)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isArchSmoothAtComplex_archDerivAtComplex_and_add_and_smul_and_comm.solution
