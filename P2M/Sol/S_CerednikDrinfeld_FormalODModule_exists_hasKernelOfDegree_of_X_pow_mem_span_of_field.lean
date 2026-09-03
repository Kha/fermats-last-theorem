import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_finite_and_projective_kerAlgebra_of_X_pow_mem
import Theorems.Thm_MvPowerSeries_free_quotient_and_finrank_quotient_map_eq_of_finite_of_isLocalRing
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_of_X_pow_mem_span_of_field
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    {k : Type} [Field k] (φ : Series k)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) ^ N ∈ Ideal.span (Set.range φ)) :
    ∃ d : ℕ, FormalODModule.HasKernelOfDegree φ d := by
  obtain ⟨hfin, hproj⟩ := CerednikDrinfeld.FormalODModule.finite_and_projective_kerAlgebra_of_X_pow_mem φ hφ0 hN
  have hfin' : Module.Finite k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range φ)) := hfin
  obtain ⟨-, hrank⟩ := MvPowerSeries.free_quotient_and_finrank_quotient_map_eq_of_finite_of_isLocalRing φ hφ0 hN hfin'
  exact ⟨Module.finrank k (FormalODModule.KerAlgebra φ), hfin, hproj, fun κ _ f => hrank κ f⟩
