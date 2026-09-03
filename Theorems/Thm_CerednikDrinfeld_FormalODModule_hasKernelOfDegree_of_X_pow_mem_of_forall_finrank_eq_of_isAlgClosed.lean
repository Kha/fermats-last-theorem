import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_of_X_pow_mem_of_forall_finrank_eq_of_isAlgClosed
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.hasKernelOfDegree_of_X_pow_mem_of_forall_finrank_eq_of_isAlgClosed
    {B : Type} [CommRing B] [IsNoetherianRing B] (φ : Series B)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range φ))
    (d : ℕ) (hdeg : ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (f : B →+* κ),
      Module.finrank κ (FormalODModule.KerAlgebra (φ.map f)) = d) :
    FormalODModule.HasKernelOfDegree φ d := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_of_X_pow_mem_of_forall_finrank_eq_of_isAlgClosed.solution
