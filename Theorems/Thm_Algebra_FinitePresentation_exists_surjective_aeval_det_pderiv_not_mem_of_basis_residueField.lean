import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FinitePresentation_exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField

set_option autoImplicit false

open TensorProduct KaehlerDifferential MvPolynomial

universe u

theorem Algebra.FinitePresentation.exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (u : Ideal S) [u.IsPrime]
    {ι : Type} [Finite ι] (w : ι → S)
    (b₀ : Module.Basis ι u.ResidueField (u.ResidueField ⊗[S] Ω[S⁄R]))
    (hb₀ : ∀ i, b₀ i = (1 : u.ResidueField) ⊗ₜ[S] D R S (w i)) :
    ∃ (m : ℕ) (x : Fin m → S) (h : Fin m → MvPolynomial (ι ⊕ Fin m) R),
      Function.Surjective (MvPolynomial.aeval (Sum.elim w x) : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] S) ∧
      (∀ a, MvPolynomial.aeval (Sum.elim w x) (h a) = 0) ∧
      MvPolynomial.aeval (Sum.elim w x)
        (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a))) ∉ u := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FinitePresentation_exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField.solution
