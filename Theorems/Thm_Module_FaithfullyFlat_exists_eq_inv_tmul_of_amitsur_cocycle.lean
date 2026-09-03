import Mathlib
import P2M.Util
import P2M.Sol.S_Module_FaithfullyFlat_exists_eq_inv_tmul_of_amitsur_cocycle

set_option autoImplicit false

universe u v

open TensorProduct

theorem Module.FaithfullyFlat.exists_eq_inv_tmul_of_amitsur_cocycle
    {R : Type u} [CommRing R] [Subsingleton (CommRing.Pic R)]
    {A : Type v} [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A]
    (u : (A ⊗[R] A)ˣ)
    (hu : Algebra.TensorProduct.map (AlgHom.id R A)
          (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A) (u : A ⊗[R] A) *
        (Algebra.TensorProduct.includeRight : A ⊗[R] A →ₐ[R] A ⊗[R] (A ⊗[R] A)) (u : A ⊗[R] A) =
      Algebra.TensorProduct.map (AlgHom.id R A)
          (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A) (u : A ⊗[R] A)) :
    ∃ a : Aˣ, (u : A ⊗[R] A) = (↑a⁻¹ : A) ⊗ₜ[R] (a : A) := by p2m_exact_reverting @_root_.P2MW.S_Module_FaithfullyFlat_exists_eq_inv_tmul_of_amitsur_cocycle.solution
