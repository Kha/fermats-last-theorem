import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_awayUnits_meetOrder_finiteIdeleDiagonal_eq_inf_map_conj
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.CosetGraph.awayUnits_meetOrder_finiteIdeleDiagonal_eq_inf_map_conj
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : QuaternionAlgebra.IsOrder R)
    (v : HeightOneSpectrum (𝓞 ℚ)) (s : (ℍ[ℚ, a, b])ˣ) :
    CerednikDrinfeld.CosetGraph.awayUnits (CerednikDrinfeld.meetOrder R (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] s)) v =
      CerednikDrinfeld.CosetGraph.awayUnits R v ⊓
        (CerednikDrinfeld.CosetGraph.awayUnits R v).map (MulAut.conj s).toMonoidHom := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_awayUnits_meetOrder_finiteIdeleDiagonal_eq_inf_map_conj.solution
