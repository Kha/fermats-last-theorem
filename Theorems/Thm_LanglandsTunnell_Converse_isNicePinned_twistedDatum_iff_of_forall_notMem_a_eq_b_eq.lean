import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_isNicePinned_twistedDatum_iff_of_forall_notMem_a_eq_b_eq

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal
theorem LanglandsTunnell.Converse.isNicePinned_twistedDatum_iff_of_forall_notMem_a_eq_b_eq
    (K : Type) [Field K] [NumberField K]
    (X Y : HeckeEigensystem K ℂ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hXY : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → X.a v = Y.a v ∧ X.b v = Y.b v)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (L Ld : ℂ → ℂ) (N : ℝ) :
    IsNicePinned (twistedDatum K X S archR archC μ uR aR uC kC) L Ld (pinnedRootNumber K X μ S archR archC uR aR uC kC) N ↔
      IsNicePinned (twistedDatum K Y S archR archC μ uR aR uC kC) L Ld (pinnedRootNumber K Y μ S archR archC uR aR uC kC) N := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_isNicePinned_twistedDatum_iff_of_forall_notMem_a_eq_b_eq.solution
