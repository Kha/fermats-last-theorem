import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_subst_injective_of_finite_kerAlgebra_of_field

set_option autoImplicit false

universe u

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.subst_injective_of_finite_kerAlgebra_of_field
    {κ : Type u} [Field κ] (φ : Series κ) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ : Module.Finite κ (FormalODModule.KerAlgebra φ))
    (f g : MvPowerSeries (Fin 2) κ) (h : MvPowerSeries.subst φ f = MvPowerSeries.subst φ g) : f = g := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_subst_injective_of_finite_kerAlgebra_of_field.solution
