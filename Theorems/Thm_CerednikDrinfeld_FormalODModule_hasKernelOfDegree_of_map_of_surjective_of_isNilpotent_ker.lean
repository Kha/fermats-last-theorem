import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_of_map_of_surjective_of_isNilpotent_ker
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.hasKernelOfDegree_of_map_of_surjective_of_isNilpotent_ker
    {R S : Type} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (π : R →+* S) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (φ : Series R) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {d : ℕ} (hd : 0 < d)
    (h : FormalODModule.HasKernelOfDegree (φ.map π) d) :
    FormalODModule.HasKernelOfDegree φ d := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_of_map_of_surjective_of_isNilpotent_ker.solution
