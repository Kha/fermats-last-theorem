import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_exists_archParams_of_continuous

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal

theorem LanglandsTunnell.Converse.exists_archParams_of_continuous (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : Continuous μ) :
    ∃ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
      (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
      (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
      (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
      (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) ∧
      (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_exists_archParams_of_continuous.solution
