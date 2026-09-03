import Mathlib
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_finite_classSet_congruenceLevel

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.finite_classSet_congruenceLevel {a b : ℚ} (ha : a < 0) (hb : b < 0)
    (Λ P : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ) (hPΛ : P ≤ Λ)
    (n : ℕ) (hn : n ≠ 0) (hnP : ∀ x ∈ Λ, (n : ℤ) • x ∈ P) :
    Finite (QuaternionAlgebra.ClassSet (QuaternionAlgebra.congruenceLevel Λ P)) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_finite_classSet_congruenceLevel.solution
