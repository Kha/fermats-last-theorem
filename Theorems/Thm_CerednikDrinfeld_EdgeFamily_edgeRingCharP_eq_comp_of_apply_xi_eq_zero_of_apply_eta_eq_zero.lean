import Mathlib
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_EdgeFamily_edgeRingCharP_eq_comp_of_apply_xi_eq_zero_of_apply_eta_eq_zero

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.EdgeFamily.edgeRingCharP.eq_comp_of_apply_xi_eq_zero_of_apply_eta_eq_zero
    (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] {Ω : Type} [CommRing Ω]
    (f₀ : EdgeFamily.edgeRingCharP p k →+* k)
    (hf₀ : f₀.comp (algebraMap k (EdgeFamily.edgeRingCharP p k)) = RingHom.id k)
    (hf₀ξ : f₀ (EdgeFamily.edgeRingCharP.ξ p k) = 0) (hf₀η : f₀ (EdgeFamily.edgeRingCharP.η p k) = 0)
    (y : EdgeFamily.edgeRingCharP p k →+* Ω)
    (hyξ : y (EdgeFamily.edgeRingCharP.ξ p k) = 0) (hyη : y (EdgeFamily.edgeRingCharP.η p k) = 0) :
    y = (y.comp (algebraMap k (EdgeFamily.edgeRingCharP p k))).comp f₀ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_EdgeFamily_edgeRingCharP_eq_comp_of_apply_xi_eq_zero_of_apply_eta_eq_zero.solution
