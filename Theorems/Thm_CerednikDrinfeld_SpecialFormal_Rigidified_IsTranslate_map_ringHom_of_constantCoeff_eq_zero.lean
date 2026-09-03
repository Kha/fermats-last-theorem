import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsTranslate_map_ringHom_of_constantCoeff_eq_zero

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsTranslate.map_ringHom_of_constantCoeff_eq_zero
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (e : Series (O ⧸ pIdeal p O)) (k m' : ℕ)
    {B B' : Type} [CommRing B] [CommRing B'] (ψ : O →+* B) (g : B →+* B')
    (t t' : Rigidified p Φ B)
    (hρ : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0) (hρ' : ∀ i, MvPowerSeries.constantCoeff (t'.ρ i) = 0)
    (he : ∀ i, MvPowerSeries.constantCoeff (e i) = 0)
    (h : Rigidified.IsTranslate e k m' ψ t t') :
    Rigidified.IsTranslate e k m' (g.comp ψ) (t.map g) (t'.map g) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsTranslate_map_ringHom_of_constantCoeff_eq_zero.solution
