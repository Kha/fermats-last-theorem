import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_exists_faithfullyFlat_forall_nonempty_algEquiv_pi

set_option autoImplicit false

open TensorProduct

universe u

theorem Algebra.Etale.exists_faithfullyFlat_forall_nonempty_algEquiv_pi
    (R : Type u) [CommRing R]
    {ι : Type} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Module.Finite R (B i)] [∀ i, Algebra.Etale R (B i)]
    (deg : ι → ℕ) (hdeg : ∀ i, Module.rankAtStalk (R := R) (B i) = deg i) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'),
      Module.Finite R R' ∧ Algebra.Etale R R' ∧ Module.FaithfullyFlat R R' ∧
      ∀ i, Nonempty (R' ⊗[R] (B i) ≃ₐ[R'] (Fin (deg i) → R')) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_exists_faithfullyFlat_forall_nonempty_algEquiv_pi.solution
