import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_exists_isArchCompAt_zero_of_isOfFinOrder

set_option autoImplicit false

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.exists_isArchCompAt_zero_of_isOfFinOrder
    (K : Type) [Field K] [NumberField K] (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχ : Continuous χ) (hfin : IsOfFinOrder χ) (w : InfinitePlace K) :
    (w.IsReal → ∃ a : ZMod 2, IsArchCompAt K χ w 0 (a.val : ℤ)) ∧
    (w.IsComplex → IsArchCompAt K χ w 0 0) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_exists_isArchCompAt_zero_of_isOfFinOrder.solution
