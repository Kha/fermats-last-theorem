import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_latticeMap_scalarGL_eq_self_of_hasDetIndex

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.latticeMap_scalarGL_eq_self_of_hasDetIndex
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) (N : Submodule 𝒪 (Fin 2 → K)) (c : Kˣ) (e : ℤ)
    (h : HasDetIndex π N e) (h' : HasDetIndex π (latticeMap (scalarGL c) N) e) : latticeMap (scalarGL c) N = N := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_latticeMap_scalarGL_eq_self_of_hasDetIndex.solution
