import Definitions.Def_NumberField_AdelicFourier
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_exists_schwartzMap_comp_ringEquiv_mixedSpace_eq_prod

set_option autoImplicit false

open NumberField NumberField.InfinitePlace MeasureTheory
open scoped SchwartzMap
open scoped Classical in

theorem NumberField.AdelicFourier.exists_schwartzMap_comp_ringEquiv_mixedSpace_eq_prod
    (F : Type) [Field F] [NumberField F]
    (t : (w : InfinitePlace F) → w.Completion)
    (U : (w : InfinitePlace F) → Set w.Completion)
    (hU : ∀ w, IsOpen (U w)) (ht : ∀ w, t w ∈ U w) :
    ∃ (g : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (gw : (w : InfinitePlace F) → w.Completion → ℂ),
      (∀ x : InfiniteAdeleRing F, g (InfiniteAdeleRing.ringEquiv_mixedSpace F x) = ∏ w, gw w (x w)) ∧
      (∀ w, Continuous (gw w)) ∧ (∀ w, HasCompactSupport (gw w)) ∧ (∀ w, tsupport (gw w) ⊆ U w) ∧
      (∀ w y, (gw w y).im = 0 ∧ 0 ≤ (gw w y).re) ∧ (∀ w, 0 < (gw w (t w)).re) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_exists_schwartzMap_comp_ringEquiv_mixedSpace_eq_prod.solution
