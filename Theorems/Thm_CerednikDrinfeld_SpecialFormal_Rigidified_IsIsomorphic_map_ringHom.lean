import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsIsomorphic_map_ringHom

set_option autoImplicit false

universe u v

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsIsomorphic.map_ringHom
    {p : ℕ} [Fact p.Prime] {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    {B B' : Type u} [CommRing B] [CommRing B'] (g : B →+* B') (t t' : Rigidified p Φ B)
    (hρ : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0) (hρ' : ∀ i, MvPowerSeries.constantCoeff (t'.ρ i) = 0)
    (h : t.IsIsomorphic t') : (t.map g).IsIsomorphic (t'.map g) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsIsomorphic_map_ringHom.solution
