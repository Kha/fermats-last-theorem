import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_dvd_of_comp
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.HasKernelOfDegree.dvd_of_comp
    {B : Type} [CommRing B] [IsNoetherianRing B] [Nontrivial B] {φ ψ : Series B} {D e : ℕ}
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (hψ0 : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0)
    (hψ : FormalODModule.HasKernelOfDegree ψ e) (hcomp : FormalODModule.HasKernelOfDegree (ψ.comp φ) D) :
    e ∣ D := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_dvd_of_comp.solution
