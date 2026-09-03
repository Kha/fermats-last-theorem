import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicClosure_linearIndependent_of_linearIndependent_rat_of_forall_apply_smul

set_option autoImplicit false

theorem AlgebraicClosure.linearIndependent_of_linearIndependent_rat_of_forall_apply_smul
    {X : Type} [MulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) X]
    {ι : Type} (F : ι → X → AlgebraicClosure ℚ)
    (hF : ∀ (i : ι) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : X),
      F i (σ • x) = σ (F i x))
    (hind : LinearIndependent ℚ F) :
    LinearIndependent (AlgebraicClosure ℚ) F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicClosure_linearIndependent_of_linearIndependent_rat_of_forall_apply_smul.solution
