import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_finite_and_projective_kerAlgebra_of_X_pow_mem
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.finite_and_projective_kerAlgebra_of_X_pow_mem
    {R : Type} [CommRing R] [IsNoetherianRing R] (φ : Series R)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ N ∈ Ideal.span (Set.range φ)) :
    Module.Finite R (FormalODModule.KerAlgebra φ) ∧ Module.Projective R (FormalODModule.KerAlgebra φ) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_finite_and_projective_kerAlgebra_of_X_pow_mem.solution
