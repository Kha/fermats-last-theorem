import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_scalarGL_iff

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_act_scalarGL_iff
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪} {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K) (c : Kˣ) :
    d.InEdgeChart π (FullLattice.act (scalarGL c) M') (FullLattice.act (scalarGL c) M) ↔ d.InEdgeChart π M' M := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_scalarGL_iff.solution
