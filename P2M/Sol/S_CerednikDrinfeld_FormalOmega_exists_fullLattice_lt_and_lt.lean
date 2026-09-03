import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Theorems.Thm_LT_LatticeTree_exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalOmega_exists_fullLattice_lt_and_lt

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π)
    (M : FullLattice 𝒪 K) :
    ∃ M' : FullLattice 𝒪 K, latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 < M'.1 ∧ M'.1 < M.1 := by
  obtain ⟨c, n, β, g₁, -, hM⟩ :=
    LT.LatticeTree.exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice 𝒪 K π hπ M.1 M.2
  refine ⟨⟨latticeMap (scalarGL c * g₁) (latticeMap (diagSnd (unitOfNeZero (K := K) hπ.ne_zero)) (stdLattice 𝒪 K)),
    ((isFullLattice_stdLattice (R := 𝒪) (K := K)).map _).map _⟩, ?_, ?_⟩
  · show latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 <
      latticeMap (scalarGL c * g₁) (latticeMap (diagSnd (unitOfNeZero (K := K) hπ.ne_zero)) (stdLattice 𝒪 K))
    rw [hM, ← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul, latticeMap_lt_latticeMap_iff]
    exact lt_of_le_of_ne (latticeMap_scalarGL_le_latticeMap_diagSnd hπ) (latticeMap_scalarGL_ne_latticeMap_diagSnd hπ)
  · show latticeMap (scalarGL c * g₁) (latticeMap (diagSnd (unitOfNeZero (K := K) hπ.ne_zero)) (stdLattice 𝒪 K)) < M.1
    conv_rhs => rw [hM]
    rw [latticeMap_lt_latticeMap_iff]
    exact latticeMap_diagSnd_lt_stdLattice hπ
