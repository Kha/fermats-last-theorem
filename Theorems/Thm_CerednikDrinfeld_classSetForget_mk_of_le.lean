import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_classSetForget_mk_of_le

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.classSetForget_mk_of_le
    {a b : ℚ} {U U' : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (h : U ≤ U') (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    CerednikDrinfeld.classSetForget U U' (QuaternionAlgebra.ClassSet.mk U x) = QuaternionAlgebra.ClassSet.mk U' x := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_classSetForget_mk_of_le.solution
