import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_localBox_meetOrder_eq_of_map_finiteAdeleEvalAt_mem_localBoxUnits
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.localBox_meetOrder_eq_of_map_finiteAdeleEvalAt_mem_localBoxUnits
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : QuaternionAlgebra.IsOrder R)
    (u : HeightOneSpectrum (𝓞 ℚ)) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hn : Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u).toRingHom.toMonoidHom n ∈ Submodule.localBoxUnits R u) :
    Submodule.localBox (CerednikDrinfeld.meetOrder R n) u = Submodule.localBox R u := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_localBox_meetOrder_eq_of_map_finiteAdeleEvalAt_mem_localBoxUnits.solution
