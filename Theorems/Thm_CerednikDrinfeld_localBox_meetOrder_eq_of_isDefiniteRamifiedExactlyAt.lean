import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_localBox_meetOrder_eq_of_isDefiniteRamifiedExactlyAt
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.localBox_meetOrder_eq_of_isDefiniteRamifiedExactlyAt
    {a b : ℚ} {p : ℕ} [Fact p.Prime] (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b p)
    (R : Submodule ℤ ℍ[ℚ, a, b]) {M : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R M)
    (u : HeightOneSpectrum (𝓞 ℚ)) (hu : ((p : ℕ) : 𝓞 ℚ) ∈ u.asIdeal)
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Submodule.localBox (CerednikDrinfeld.meetOrder R m) u = Submodule.localBox R u := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_localBox_meetOrder_eq_of_isDefiniteRamifiedExactlyAt.solution
