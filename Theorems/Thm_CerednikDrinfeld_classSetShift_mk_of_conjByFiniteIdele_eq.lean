import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_classSetShift_mk_of_conjByFiniteIdele_eq
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.classSetShift_mk_of_conjByFiniteIdele_eq
    {a b : ℚ} (O : Submodule ℤ ℍ[ℚ, a, b]) (hO : QuaternionAlgebra.IsOrder O)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : Submodule.conjByFiniteIdele O n = O) (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    CerednikDrinfeld.classSetShift (Submodule.finiteIdeleStabilizer O) n
        (QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer O) x) =
      QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer O) (x * n) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_classSetShift_mk_of_conjByFiniteIdele_eq.solution
