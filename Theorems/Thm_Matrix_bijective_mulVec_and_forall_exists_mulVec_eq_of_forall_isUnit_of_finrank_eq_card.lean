import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_bijective_mulVec_and_forall_exists_mulVec_eq_of_forall_isUnit_of_finrank_eq_card

set_option autoImplicit false

theorem Matrix.bijective_mulVec_and_forall_exists_mulVec_eq_of_forall_isUnit_of_finrank_eq_card
    {K : Type} [Field K] {D : Type} [Ring D] [Algebra K D]
    (hdiv : ∀ d : D, d ≠ 0 → IsUnit d)
    {N : Type} [Fintype N] [DecidableEq N] [Nonempty N]
    (hdim : Module.finrank K D = Fintype.card N)
    (ι : D →ₐ[K] Matrix N N K) (e₀ : N → K) (he₀ : e₀ ≠ 0) :
    Function.Bijective (fun d : D => (ι d).mulVec e₀) ∧
      ∀ T : Matrix N N K, (∀ d : D, T * ι d = ι d * T) →
        ∃ ξ : D, ∀ d : D, T.mulVec ((ι d).mulVec e₀) = (ι (d * ξ)).mulVec e₀ := by p2m_exact_reverting @_root_.P2MW.S_Matrix_bijective_mulVec_and_forall_exists_mulVec_eq_of_forall_isUnit_of_finrank_eq_card.solution
