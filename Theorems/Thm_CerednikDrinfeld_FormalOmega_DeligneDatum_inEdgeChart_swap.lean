import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_swap

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_swap
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (c : Kˣ) (hc : (c : K) = algebraMap 𝒪 K π)
    {d : DeligneDatum (K := K) π B} {M' M : FullLattice 𝒪 K} (hd : d.InEdgeChart π M' M) :
    d.InEdgeChart π (FullLattice.act (scalarGL c) M) M' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_swap.solution
