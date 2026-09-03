import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_eq_of_le_of_hasDetIndex_padic

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega LT.LatticeTree

open scoped PadicInt Padic

theorem LT.LatticeTree.eq_of_le_of_hasDetIndex_padic
    (p : ℕ) [Fact p.Prime] (N N' : Submodule ℤ_[p] (Fin 2 → ℚ_[p])) (hle : N ≤ N') (e : ℤ)
    (hN : HasDetIndex (K := ℚ_[p]) (p : ℤ_[p]) N e) (hN' : HasDetIndex (K := ℚ_[p]) (p : ℤ_[p]) N' e) :
    N = N' := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_eq_of_le_of_hasDetIndex_padic.solution
