import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_finite_stabilizer_projAwayUnits_vert_of_isOrder
attribute [-simp] QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.CosetGraph.finite_stabilizer_projAwayUnits_vert_of_isOrder
    {a b : ℚ} (ha : a < 0) (hb : b < 0) {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R)
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : CosetGraph.Vert R v) :
    Finite ↥(MulAction.stabilizer (CosetGraph.ProjAwayUnits R v) x) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_finite_stabilizer_projAwayUnits_vert_of_isOrder.solution
