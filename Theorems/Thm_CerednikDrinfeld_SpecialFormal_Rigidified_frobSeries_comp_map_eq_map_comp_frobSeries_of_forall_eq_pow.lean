import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_frobSeries_comp_map_eq_map_comp_frobSeries_of_forall_eq_pow

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.frobSeries_comp_map_eq_map_comp_frobSeries_of_forall_eq_pow
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {B : Type} [CommRing B]
    (ψ χ : O →+* B) (j : ℕ)
    (hχ : ∀ x : O ⧸ pIdeal p O, residueMap ψ x = (residueMap χ x) ^ (p ^ j))
    (e : Series (O ⧸ pIdeal p O)) (he : ∀ i, MvPowerSeries.constantCoeff (e i) = 0) :
    (Rigidified.frobSeries (p := p) (B ⧸ pIdeal p B) j).comp (Series.map (residueMap χ) e) =
      (Series.map (residueMap ψ) e).comp (Rigidified.frobSeries (p := p) (B ⧸ pIdeal p B) j) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_frobSeries_comp_map_eq_map_comp_frobSeries_of_forall_eq_pow.solution
