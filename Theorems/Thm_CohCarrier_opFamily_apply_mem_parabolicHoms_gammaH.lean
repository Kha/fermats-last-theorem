import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_CohCarrier_opFamily_apply_mem_parabolicHoms_gammaH

set_option autoImplicit false

theorem CohCarrier.opFamily_apply_mem_parabolicHoms_gammaH (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] (g : CohCarrier.Gen N S) (φ : CohCarrier.H1 N H 𝒪)
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) 𝒪) :
    CohCarrier.opFamily N H S 𝒪 g φ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) 𝒪 := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_opFamily_apply_mem_parabolicHoms_gammaH.solution
