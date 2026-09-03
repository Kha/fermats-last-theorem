import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_le_and_of_comp_pow
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.HasKernelOfDegree.le_and_of_comp_pow
    {r : ℕ} [Fact r.Prime] {B : Type} [CommRing B] [IsNoetherianRing B] [Nontrivial B] {φ ψ : Series B}
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (hψ0 : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0)
    {d D : ℕ} (hφ : FormalODModule.HasKernelOfDegree φ (r ^ d))
    (hcomp : FormalODModule.HasKernelOfDegree (ψ.comp φ) (r ^ D)) :
    d ≤ D ∧ FormalODModule.HasKernelOfDegree ψ (r ^ (D - d)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_le_and_of_comp_pow.solution
