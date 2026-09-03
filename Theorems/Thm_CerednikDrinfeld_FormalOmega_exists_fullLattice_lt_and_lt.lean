import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_exists_fullLattice_lt_and_lt

set_option autoImplicit false

open scoped TensorProduct
p2m_open "LT.LatticeTree~exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice CerednikDrinfeld CerednikDrinfeld.FormalOmega"

theorem CerednikDrinfeld.FormalOmega.exists_fullLattice_lt_and_lt
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π)
    (M : FullLattice 𝒪 K) :
    ∃ M' : FullLattice 𝒪 K, latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 < M'.1 ∧ M'.1 < M.1 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_exists_fullLattice_lt_and_lt.solution
