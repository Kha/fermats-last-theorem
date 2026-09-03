import Definitions.Def_LatticeTreeOrbital
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice

set_option autoImplicit false

open LT.LatticeTree

theorem LT.LatticeTree.exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) :
    ∃ (c : Kˣ) (n : ℤ) (β : K) (g : Matrix.GeneralLinearGroup (Fin 2) K),
      (g : Matrix (Fin 2) (Fin 2) K) = !![algebraMap R K ϖ ^ n, β; 0, 1] ∧
      L = latticeMap (scalarGL c * g) (stdLattice R K) := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice.solution
