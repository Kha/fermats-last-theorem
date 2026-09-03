import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import P2M.Util
import P2M.Sol.S_AutomorphicForm_archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) (n : ℕ)
    (hwt : archDerivAtComplex hw .iH φ = (Complex.I * (n : ℂ)) • φ)
    (hJ : archDerivAtComplex hw .Fm φ - archDerivAtComplex hw .E φ
      + Complex.I • (archDerivAtComplex hw .iE φ + archDerivAtComplex hw .iFm φ) = 0) :
    archKCasimirAtComplex hw φ = (-(((n : ℂ) ^ 2 + 2 * (n : ℂ)))) • φ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_archKCasimirAtComplex_eq_smul_of_archDerivAtComplex_iH_eq_smul_of_compactRaise_eq_zero.solution
