import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_subst_injective_of_hasKernelOfDegree

set_option autoImplicit false

universe u

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.subst_injective_of_hasKernelOfDegree
    {B : Type u} [CommRing B] [IsNoetherianRing B] (φ : Series B) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    {d : ℕ} (hφ : FormalODModule.HasKernelOfDegree φ d)
    (f g : MvPowerSeries (Fin 2) B) (h : MvPowerSeries.subst φ f = MvPowerSeries.subst φ g) : f = g := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_subst_injective_of_hasKernelOfDegree.solution
