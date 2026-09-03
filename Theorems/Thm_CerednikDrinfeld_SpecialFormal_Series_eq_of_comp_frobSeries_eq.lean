import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Series_eq_of_comp_frobSeries_eq

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Series.eq_of_comp_frobSeries_eq
    {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (j : ℕ) (φ ψ : Series B)
    (h : φ.comp (Rigidified.frobSeries (p := p) B j) = ψ.comp (Rigidified.frobSeries (p := p) B j)) :
    φ = ψ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Series_eq_of_comp_frobSeries_eq.solution
