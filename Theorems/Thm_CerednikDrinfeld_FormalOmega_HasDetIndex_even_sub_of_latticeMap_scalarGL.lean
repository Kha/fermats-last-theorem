import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_HasDetIndex_even_sub_of_latticeMap_scalarGL

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.HasDetIndex.even_sub_of_latticeMap_scalarGL
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) (N : Submodule 𝒪 (Fin 2 → K)) (c : Kˣ) (e e' : ℤ)
    (h : HasDetIndex π N e) (h' : HasDetIndex π (latticeMap (scalarGL c) N) e') : Even (e - e') := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_HasDetIndex_even_sub_of_latticeMap_scalarGL.solution
