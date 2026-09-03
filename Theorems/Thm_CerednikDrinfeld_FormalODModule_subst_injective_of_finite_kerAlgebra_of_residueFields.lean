import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_subst_injective_of_finite_kerAlgebra_of_residueFields

set_option autoImplicit false

universe u

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.subst_injective_of_finite_kerAlgebra_of_residueFields
    {B : Type u} [CommRing B] [IsNoetherianRing B] (φ : Series B)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ : Module.Finite B (FormalODModule.KerAlgebra φ))
    (hres : ∀ (κ : Type u) [Field κ] (g : B →+* κ), Function.Surjective g →
      Module.Finite κ (FormalODModule.KerAlgebra (φ.map g)) →
      ∀ f' g' : MvPowerSeries (Fin 2) κ,
        MvPowerSeries.subst (φ.map g) f' = MvPowerSeries.subst (φ.map g) g' → f' = g')
    (f g : MvPowerSeries (Fin 2) B) (h : MvPowerSeries.subst φ f = MvPowerSeries.subst φ g) : f = g := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_subst_injective_of_finite_kerAlgebra_of_residueFields.solution
