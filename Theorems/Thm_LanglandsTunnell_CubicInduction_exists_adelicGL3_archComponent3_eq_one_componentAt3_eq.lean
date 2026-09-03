import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_adelicGL3_archComponent3_eq_one_componentAt3_eq
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_adelicGL3_archComponent3_eq_one_componentAt3_eq
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (y : GL (Fin 3) (v.adicCompletion K)) :
    ∃ k : AdelicGL 3 (𝓞 K) K,
      archComponent3 (𝓞 K) K k = 1 ∧ componentAt3 (𝓞 K) K v k = y ∧
      ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v → componentAt3 (𝓞 K) K w k = 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_adelicGL3_archComponent3_eq_one_componentAt3_eq.solution
