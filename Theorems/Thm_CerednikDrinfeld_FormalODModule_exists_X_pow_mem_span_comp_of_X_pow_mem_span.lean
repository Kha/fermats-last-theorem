import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_comp_of_X_pow_mem_span

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_comp_of_X_pow_mem_span
    {B : Type} [CommRing B] {φ ψ : Series B}
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ : ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range φ))
    (hψ : ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range ψ)) :
    ∃ N : ℕ, ∀ i : Fin 2,
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range (ψ.comp φ)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_comp_of_X_pow_mem_span.solution
