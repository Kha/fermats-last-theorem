import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Projective_exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat

universe u

set_option autoImplicit false

open TensorProduct

theorem Module.Projective.exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (P₁ P₂ : Type u) [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₁] [Module R P₂]
    [Module.Projective R P₁] [Module.Finite R P₁]
    [Module.Projective R P₂] [Module.Finite R P₂]
    (e : ((R ⧸ I) ⊗[R] P₁) ≃ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] P₂)) :
    ∃ σ' : P₁ ≃ₗ[R] P₂, ∀ p : P₁, (1 : R ⧸ I) ⊗ₜ[R] σ' p = e ((1 : R ⧸ I) ⊗ₜ[R] p) := by p2m_exact_reverting @_root_.P2MW.S_Module_Projective_exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat.solution
