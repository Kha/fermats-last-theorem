import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_Order_FiniteIdele
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_conjByFiniteIdele

open scoped TensorProduct Pointwise Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsOrder.conjByFiniteIdele
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ) (β : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    QuaternionAlgebra.IsOrder (Submodule.conjByFiniteIdele Λ β) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_conjByFiniteIdele.solution
