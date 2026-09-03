import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_inertia_asIdeal_pow_succ_eq_map_subtype_lowerRamificationGroup

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem IsDedekindDomain.HeightOneSpectrum.inertia_asIdeal_pow_succ_eq_map_subtype_lowerRamificationGroup
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (w : HeightOneSpectrum (𝓞 F)) (i : ℕ) :
    (w.asIdeal ^ (i + 1)).inertia (F ≃ₐ[E] F) =
      (((w.valuation F).valuationSubring).lowerRamificationGroup E i).map
        (((w.valuation F).valuationSubring).decompositionSubgroup E).subtype := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_inertia_asIdeal_pow_succ_eq_map_subtype_lowerRamificationGroup.solution
