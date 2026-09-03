import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp_map_of_field
    {R : Type u} [CommRing R] {κ : Type u} [Field κ] (f : κ →+* R)
    {ψ : Series R} {a : ℕ} (hψ : FormalODModule.HasKernelOfDegree ψ a)
    {φ : Series κ} {b : ℕ} (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ : FormalODModule.HasKernelOfDegree φ b) :
    FormalODModule.HasKernelOfDegree (ψ.comp (φ.map f)) (a * b) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field.solution
