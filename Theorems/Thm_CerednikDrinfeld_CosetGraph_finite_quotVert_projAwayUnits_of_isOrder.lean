import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_finite_quotVert_projAwayUnits_of_isOrder
attribute [-simp] QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "IsDedekindDomain NumberField QuaternionAlgebra~ClassSet~finite_classSet_congruenceLevel CerednikDrinfeld"

theorem CerednikDrinfeld.CosetGraph.finite_quotVert_projAwayUnits_of_isOrder
    {a b : ℚ} (ha : a < 0) (hb : b < 0) {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Finite (Mumford.QuotVert (CosetGraph.ProjAwayUnits R v) (CosetGraph.Vert R v)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_finite_quotVert_projAwayUnits_of_isOrder.solution
