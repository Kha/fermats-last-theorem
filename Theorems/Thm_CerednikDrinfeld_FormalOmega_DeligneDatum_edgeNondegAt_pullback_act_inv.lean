import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_pullback_act_inv

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.edgeNondegAt_pullback_act_inv
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d : DeligneDatum (K := K) π B) (h : Matrix.GeneralLinearGroup (Fin 2) K) (𝔭 : Ideal B) (N' N : FullLattice 𝒪 K)
    (hN : d.EdgeNondegAt π 𝔭 N' N) :
    (DeligneDatum.pullback π B h d).EdgeNondegAt π 𝔭 (FullLattice.act h⁻¹ N') (FullLattice.act h⁻¹ N) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_pullback_act_inv.solution
