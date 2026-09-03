import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidAlgebra_ringKrullDim_pi_fin_int_eq

set_option autoImplicit false

theorem AddMonoidAlgebra.ringKrullDim_pi_fin_int_eq (κ : Type*) [Field κ] (t : ℕ) :
    ringKrullDim (AddMonoidAlgebra κ (Fin t → ℤ)) = t := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidAlgebra_ringKrullDim_pi_fin_int_eq.solution
