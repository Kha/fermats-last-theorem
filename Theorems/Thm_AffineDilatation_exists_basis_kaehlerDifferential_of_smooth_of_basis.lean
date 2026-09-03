import Mathlib
import Definitions.Def_RingTheory_AffineDilatation
import P2M.Util
import P2M.Sol.S_AffineDilatation_exists_basis_kaehlerDifferential_of_smooth_of_basis

set_option autoImplicit false

open TensorProduct KaehlerDifferential

universe u

theorem AffineDilatation.exists_basis_kaehlerDifferential_of_smooth_of_basis
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {C : Type u} [CommRing C] [Algebra R C] [Algebra.Smooth R C]
    {r n : ℕ} (y : Fin r → C) (z : Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R])
    (hby : ∀ i, b (Sum.inl i) = D R C (y i)) (hbz : ∀ j, b (Sum.inr j) = D R C (z j)) :
    ∃ b' : Module.Basis (Fin r ⊕ Fin n)
        (AffineDilatation.Ring (Ideal.span (insert (algebraMap R C π) (Set.range z))) (algebraMap R C π))
        Ω[AffineDilatation.Ring (Ideal.span (insert (algebraMap R C π) (Set.range z))) (algebraMap R C π)⁄R],
      (∀ i, b' (Sum.inl i) =
        D R (AffineDilatation.Ring (Ideal.span (insert (algebraMap R C π) (Set.range z))) (algebraMap R C π))
          (algebraMap C _ (y i))) ∧
      (∀ j, (algebraMap R
          (AffineDilatation.Ring (Ideal.span (insert (algebraMap R C π) (Set.range z))) (algebraMap R C π)) π) •
          b' (Sum.inr j) =
        D R (AffineDilatation.Ring (Ideal.span (insert (algebraMap R C π) (Set.range z))) (algebraMap R C π))
          (algebraMap C _ (z j))) := by p2m_exact_reverting @_root_.P2MW.S_AffineDilatation_exists_basis_kaehlerDifferential_of_smooth_of_basis.solution
