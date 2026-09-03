import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Projective_nonempty_linearEquiv_of_baseChange_quotient_of_squareZero

universe u

set_option autoImplicit false

open TensorProduct

theorem Module.Projective.nonempty_linearEquiv_of_baseChange_quotient_of_squareZero
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (P₁ P₂ : Type u) [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₁] [Module R P₂]
    [Module.Projective R P₁] [Module.Finite R P₁]
    [Module.Projective R P₂] [Module.Finite R P₂]
    (e : ((R ⧸ I) ⊗[R] P₁) ≃ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] P₂)) :
    Nonempty (P₁ ≃ₗ[R] P₂) := by p2m_exact_reverting @_root_.P2MW.S_Module_Projective_nonempty_linearEquiv_of_baseChange_quotient_of_squareZero.solution
