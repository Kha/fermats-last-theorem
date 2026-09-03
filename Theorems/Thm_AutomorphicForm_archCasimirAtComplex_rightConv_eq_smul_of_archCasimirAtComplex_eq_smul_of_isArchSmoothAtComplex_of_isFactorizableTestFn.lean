import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_archCasimirAtComplex_rightConv_eq_smul_of_archCasimirAtComplex_eq_smul_of_isArchSmoothAtComplex_of_isFactorizableTestFn
attribute [-simp] AutomorphicForm.CuspidalConstituent.rightRegular_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.archCasimirAtComplex_rightConv_eq_smul_of_archCasimirAtComplex_eq_smul_of_isArchSmoothAtComplex_of_isFactorizableTestFn
    (K : Type) [Field K] [NumberField K] (w : InfinitePlace K) (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ) (hs : IsArchSmoothAtComplex hw φ)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d φ))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' φ)))
    (lam lam' : ℂ) (hΩ : archCasimirAtComplex hw φ = lam • φ) (hΩb : archCasimirBarAtComplex hw φ = lam' • φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f) :
    IsArchSmoothAtComplex hw (rightConv K φ f) ∧
      archCasimirAtComplex hw (rightConv K φ f) = lam • rightConv K φ f ∧
      archCasimirBarAtComplex hw (rightConv K φ f) = lam' • rightConv K φ f := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_archCasimirAtComplex_rightConv_eq_smul_of_archCasimirAtComplex_eq_smul_of_isArchSmoothAtComplex_of_isFactorizableTestFn.solution
