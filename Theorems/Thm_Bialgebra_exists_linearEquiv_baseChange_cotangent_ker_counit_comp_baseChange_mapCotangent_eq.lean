import Mathlib
import P2M.Util
import P2M.Sol.S_Bialgebra_exists_linearEquiv_baseChange_cotangent_ker_counit_comp_baseChange_mapCotangent_eq

open scoped TensorProduct

theorem Bialgebra.exists_linearEquiv_baseChange_cotangent_ker_counit_comp_baseChange_mapCotangent_eq
    (R : Type) [CommRing R] (S : Type) [CommRing S] [Algebra R S]
    (A : Type) [CommRing A] [Bialgebra R A] :
    ∃ Λ : S ⊗[R] (RingHom.ker (Bialgebra.counitAlgHom R A)).Cotangent ≃ₗ[S]
        (RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] A))).Cotangent,
      (∀ (s : S) (x : ↥(RingHom.ker (Bialgebra.counitAlgHom R A)))
          (y : ↥(RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] A)))),
          (y : S ⊗[R] A) = s ⊗ₜ[R] (x : A) →
          Λ (s ⊗ₜ[R] (RingHom.ker (Bialgebra.counitAlgHom R A)).toCotangent x) =
            (RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] A))).toCotangent y) ∧
      ∀ (q : A →ₐ[R] A)
        (hq : RingHom.ker (Bialgebra.counitAlgHom R A) ≤
          (RingHom.ker (Bialgebra.counitAlgHom R A)).comap q)
        (hQ : RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] A)) ≤
          (RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] A))).comap
            (Algebra.TensorProduct.map (AlgHom.id S S) q)),
        (Λ : S ⊗[R] (RingHom.ker (Bialgebra.counitAlgHom R A)).Cotangent →ₗ[S]
            (RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] A))).Cotangent) ∘ₗ
          ((RingHom.ker (Bialgebra.counitAlgHom R A)).mapCotangent
              (RingHom.ker (Bialgebra.counitAlgHom R A)) q hq).baseChange S =
        (RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] A))).mapCotangent
            (RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] A)))
            (Algebra.TensorProduct.map (AlgHom.id S S) q) hQ ∘ₗ
          (Λ : S ⊗[R] (RingHom.ker (Bialgebra.counitAlgHom R A)).Cotangent →ₗ[S]
            (RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] A))).Cotangent) := by p2m_exact_reverting @_root_.P2MW.S_Bialgebra_exists_linearEquiv_baseChange_cotangent_ker_counit_comp_baseChange_mapCotangent_eq.solution
