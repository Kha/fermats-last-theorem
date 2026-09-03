import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Projective_exists_baseChange_quotient_iso_of_squareZero

universe u

set_option autoImplicit false

open TensorProduct

theorem Module.Projective.exists_baseChange_quotient_iso_of_squareZero
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (P : Type u) [AddCommGroup P] [Module (R ⧸ I) P]
    [Module.Projective (R ⧸ I) P] [Module.Finite (R ⧸ I) P] :
    ∃ (P' : Type u) (_ : AddCommGroup P') (_ : Module R P'),
      Module.Projective R P' ∧ Module.Finite R P' ∧
      Nonempty (((R ⧸ I) ⊗[R] P') ≃ₗ[R ⧸ I] P) := by p2m_exact_reverting @_root_.P2MW.S_Module_Projective_exists_baseChange_quotient_iso_of_squareZero.solution
