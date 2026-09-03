import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_iff_of_isBaseChange_of_isLocalHom

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_iff_of_isBaseChange_of_isLocalHom
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B] [IsLocalRing B]
    {B' : Type} [CommRing B'] [Algebra 𝒪 B'] [IsLocalRing B'] (f : B →ₐ[𝒪] B') [IsLocalHom f]
    (d : DeligneDatum (K := K) π B) (d' : DeligneDatum (K := K) π B')
    (hd' : DeligneDatum.IsBaseChange (K := K) (π := π) f d d') (M' M : FullLattice 𝒪 K) :
    d'.InEdgeChart π M' M ↔ d.InEdgeChart π M' M := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_iff_of_isBaseChange_of_isLocalHom.solution
