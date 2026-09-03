import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_pt_iff_inEdgeChart_pt_zero

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.FormalOmega.AdicPoint.inEdgeChart_pt_iff_inEdgeChart_pt_zero
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪}
    {R : Type} [CommRing R] [Algebra 𝒪 R] (x : AdicPoint K π R) (n : ℕ) (M' M : FullLattice 𝒪 K) :
    (x.pt n).InEdgeChart π M' M ↔ (x.pt 0).InEdgeChart π M' M := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_inEdgeChart_pt_iff_inEdgeChart_pt_zero.solution
