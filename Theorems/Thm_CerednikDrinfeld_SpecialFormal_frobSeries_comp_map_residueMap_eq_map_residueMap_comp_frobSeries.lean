import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_frobSeries_comp_map_residueMap_eq_map_residueMap_comp_frobSeries

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.frobSeries_comp_map_residueMap_eq_map_residueMap_comp_frobSeries
    {r : ℕ} [Fact r.Prime] {O B : Type} [CommRing O] [CommRing B] (ψ₁ ψ₂ : O →+* B)
    (h : ∀ x : O, ψ₁ x ^ r - ψ₂ x ∈ pIdeal r B)
    (β : Series (O ⧸ pIdeal r O)) (hβ : ∀ i, MvPowerSeries.constantCoeff (β i) = 0) :
    (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) 1).comp (Series.map (residueMap ψ₁) β) =
      (Series.map (residueMap ψ₂) β).comp (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) 1) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_frobSeries_comp_map_residueMap_eq_map_residueMap_comp_frobSeries.solution
