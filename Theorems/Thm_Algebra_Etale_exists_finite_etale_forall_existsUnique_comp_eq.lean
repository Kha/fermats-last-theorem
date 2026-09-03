import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_exists_finite_etale_forall_existsUnique_comp_eq

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.Etale.exists_finite_etale_forall_existsUnique_comp_eq
    (S B : Type) [CommRing S] [CommRing B] [Algebra S B] [Module.Finite S B] [Algebra.Etale S B] (m : ℕ) :
    ∃ (C : Type) (_ : CommRing C) (_ : Algebra S C) (_ : Module.Finite S C) (_ : Algebra.Etale S C)
      (u : Fin m → (B →ₐ[S] C)),
      ∀ (D : Type) [CommRing D] [Algebra S D] (v : Fin m → (B →ₐ[S] D)),
        ∃! w : C →ₐ[S] D, ∀ i, w.comp (u i) = v i := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_exists_finite_etale_forall_existsUnique_comp_eq.solution
