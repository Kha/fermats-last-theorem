import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_eq_of_isODHom_of_act_pow_comp_map_comp_eq

set_option autoImplicit false

universe u v

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.eq_of_isODHom_of_act_pow_comp_map_comp_eq
    {p : ℕ} [Fact p.Prime] {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    {B : Type u} [CommRing B] [IsNoetherianRing B] (hB : IsNilpotent (p : B))
    (ι : Zp2 p →+* O) (ψ : O →+* B) (t t' : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (hρ' : ∀ i, MvPowerSeries.constantCoeff (t'.ρ i) = 0)
    (u₁ u₂ : Series B) (m₁ m₂ : ℕ)
    (hu₁ : FormalODModule.IsODHom t.X t'.X u₁) (hu₂ : FormalODModule.IsODHom t.X t'.X u₂)
    (h₁ : (t'.Xbar.act ((p : Zp2 p) ^ (m₁ + t'.n))).comp
        ((u₁.map (Ideal.Quotient.mk (pIdeal p B))).comp t.ρ) =
      (t'.Xbar.act ((p : Zp2 p) ^ (m₁ + t.n))).comp t'.ρ)
    (h₂ : (t'.Xbar.act ((p : Zp2 p) ^ (m₂ + t'.n))).comp
        ((u₂.map (Ideal.Quotient.mk (pIdeal p B))).comp t.ρ) =
      (t'.Xbar.act ((p : Zp2 p) ^ (m₂ + t.n))).comp t'.ρ) :
    u₁ = u₂ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_eq_of_isODHom_of_act_pow_comp_map_comp_eq.solution
