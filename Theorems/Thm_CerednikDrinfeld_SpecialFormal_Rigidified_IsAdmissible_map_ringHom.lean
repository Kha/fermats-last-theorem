import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom

set_option autoImplicit false

universe u v

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom
    {p : ℕ} [Fact p.Prime] {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (ι : Zp2 p →+* O) {B B' : Type u} [CommRing B] [IsNoetherianRing B] [CommRing B']
    (ψ : O →+* B) (g : B →+* B') (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) :
    (t.map g).IsAdmissible ι (g.comp ψ) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom.solution
