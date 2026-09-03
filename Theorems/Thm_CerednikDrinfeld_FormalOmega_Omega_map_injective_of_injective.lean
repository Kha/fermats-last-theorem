import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_Omega_map_injective_of_injective

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.Omega.map_injective_of_injective
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {S' B' : Type} [CommRing S'] [Algebra 𝒪 S'] [CommRing B'] [Algebra 𝒪 B'] (φ : S' →ₐ[𝒪] B')
    (hφ : Function.Injective φ) : Function.Injective ((Omega K π).map φ) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_Omega_map_injective_of_injective.solution
