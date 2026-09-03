import Mathlib
import Definitions.Def_RingTheory_AffineDilatation
import P2M.Util
import P2M.Sol.S_AffineDilatation_nonempty_algEquiv_mvPolynomial_sum

set_option autoImplicit false

universe u v

theorem AffineDilatation.nonempty_algEquiv_mvPolynomial_sum
    {R : Type u} [CommRing R] (π : R) (hπ : IsSMulRegular R π) (σ : Type v) (τ : Type v) :
    ∃ e : AffineDilatation.Ring
          (Ideal.span (insert (MvPolynomial.C π) (Set.range fun j : τ => (MvPolynomial.X (Sum.inr j) : MvPolynomial (σ ⊕ τ) R))))
          (MvPolynomial.C π) ≃ₐ[R] MvPolynomial (σ ⊕ τ) R,
      (∀ i : σ, e (algebraMap (MvPolynomial (σ ⊕ τ) R) _ (MvPolynomial.X (Sum.inl i))) = MvPolynomial.X (Sum.inl i)) ∧
      (∀ j : τ, e (AffineDilatation.divElem _ (MvPolynomial.C π) (MvPolynomial.X (Sum.inr j))
          (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩))) = MvPolynomial.X (Sum.inr j)) ∧
      (∀ j : τ, e (algebraMap (MvPolynomial (σ ⊕ τ) R) _ (MvPolynomial.X (Sum.inr j))) =
          MvPolynomial.C π * MvPolynomial.X (Sum.inr j)) := by p2m_exact_reverting @_root_.P2MW.S_AffineDilatation_nonempty_algEquiv_mvPolynomial_sum.solution
