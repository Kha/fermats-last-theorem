import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_isODHom_of_comp_map_eq_of_surjective_of_isNilpotent

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isIsomorphic_of_isODHom_of_comp_map_eq_of_surjective_of_isNilpotent
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O) {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    {R S : Type} [CommRing R] [CommRing S]
    (π : R →+* S) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π)) (hR : IsNilpotent (p : R))
    (ψ : O →+* R) (t₁ t₂ : Rigidified p Φ R) (h₁ : t₁.IsAdmissible ι ψ) (h₂ : t₂.IsAdmissible ι ψ)
    (u v : Series R) (hu : FormalODModule.IsODHom t₁.X t₂.X u) (hv : FormalODModule.IsODHom t₂.X t₁.X v)
    (hvu : v.comp u = Series.id R) (huv : u.comp v = Series.id R) (m : ℕ)
    (hc : ((t₂.map π).Xbar.act ((p : Zp2 p) ^ (m + t₂.n))).comp
        (((u.map π).map (Ideal.Quotient.mk (pIdeal p S))).comp (t₁.map π).ρ)
      = ((t₂.map π).Xbar.act ((p : Zp2 p) ^ (m + t₁.n))).comp (t₂.map π).ρ) :
    t₁.IsIsomorphic t₂ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_isODHom_of_comp_map_eq_of_surjective_of_isNilpotent.solution
