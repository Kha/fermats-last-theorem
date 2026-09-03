import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt

set_option autoImplicit false

open scoped TensorProduct
p2m_open "LT.LatticeTree~exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice CerednikDrinfeld CerednikDrinfeld.FormalOmega"

theorem CerednikDrinfeld.FormalOmega.exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (M' M : FullLattice 𝒪 K)
    (h₁ : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 < M'.1) (h₂ : M'.1 < M.1) :
    ∃ h : Matrix.GeneralLinearGroup (Fin 2) K,
      FullLattice.act h (stdFullLattice K) = M ∧ FullLattice.act h (FullLattice.act g (stdFullLattice K)) = M' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt.solution
