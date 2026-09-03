import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_indefinite_forall_isUnit_adicCompletion_iff_mem_or_mem

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.exists_indefinite_forall_isUnit_adicCompletion_iff_mem_or_mem
    (q q' : ℕ) (hq : q.Prime) (hq' : q'.Prime) (hqq' : q' ≠ q) :
    ∃ a b : ℚ, (0 < a ∨ 0 < b) ∧
      ∀ v : HeightOneSpectrum (𝓞 ℚ),
        (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) ↔
          ((q : 𝓞 ℚ) ∈ v.asIdeal ∨ (q' : 𝓞 ℚ) ∈ v.asIdeal) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_indefinite_forall_isUnit_adicCompletion_iff_mem_or_mem.solution
