import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_exists_basis_span_eq

open scoped Quaternion

theorem QuaternionAlgebra.IsOrder.exists_basis_span_eq {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) :
    ∃ B : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b], (∀ i, B i ∈ Λ) ∧ Submodule.span ℤ (Set.range B) = Λ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_exists_basis_span_eq.solution
