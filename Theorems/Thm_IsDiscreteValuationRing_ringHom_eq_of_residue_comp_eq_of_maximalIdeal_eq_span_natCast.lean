import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_ringHom_eq_of_residue_comp_eq_of_maximalIdeal_eq_span_natCast

set_option autoImplicit false

open IsLocalRing FormalGroup

theorem IsDiscreteValuationRing.ringHom_eq_of_residue_comp_eq_of_maximalIdeal_eq_span_natCast
    (q : ℕ) [Fact q.Prime]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀]
    (hW₀ : IsLocalRing.maximalIdeal W₀ = Ideal.span {(q : W₀)})
    [PerfectRing (ResidueField W₀) q]
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T]
    (f g : W₀ →+* T) [IsLocalHom f] [IsLocalHom g]
    (hfg : (residue T).comp f = (residue T).comp g) :
    f = g := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_ringHom_eq_of_residue_comp_eq_of_maximalIdeal_eq_span_natCast.solution
