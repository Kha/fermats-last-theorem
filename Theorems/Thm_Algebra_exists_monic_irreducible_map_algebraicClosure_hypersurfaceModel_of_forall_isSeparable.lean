import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_monic_irreducible_map_algebraicClosure_hypersurfaceModel_of_forall_isSeparable

set_option autoImplicit false

universe u v w

theorem Algebra.exists_monic_irreducible_map_algebraicClosure_hypersurfaceModel_of_forall_isSeparable
    (k : Type u) [Field k] {R : Type v} {C : Type w} [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [CommRing C] [IsDomain C] [Algebra k C] [Algebra R C]
    [IsScalarTower k R C] [Algebra.FiniteType R C] [FaithfulSMul R C]
    (hgi : ∀ θ : FractionRing C,
      IsSeparable (IntermediateField.adjoin k (Set.range (algebraMap R (FractionRing C)))) θ →
      θ ∈ IntermediateField.adjoin k (Set.range (algebraMap R (FractionRing C)))) :
    ∃ r : R, r ≠ 0 ∧ ∃ (d : ℕ) (z : Fin d → C) (w : C) (F : Polynomial (MvPolynomial (Fin d) R))
      (g : MvPolynomial (Fin d) R),
      AlgebraicIndependent R z ∧ F.Monic ∧
      F.eval₂ (MvPolynomial.aeval z : MvPolynomial (Fin d) R →ₐ[R] C).toRingHom w = 0 ∧
      Irreducible (F.map (MvPolynomial.map (algebraMap R (AlgebraicClosure (FractionRing R))))) ∧
      g ≠ 0 ∧
      (∀ c : C, ∃ m M : ℕ, 0 < M ∧
        ((MvPolynomial.aeval z g) ^ m * c) ^ M ∈ Algebra.adjoin R (insert w (Set.range z))) ∧
      (∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin R (Set.range z)) (r ^ n • c)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_monic_irreducible_map_algebraicClosure_hypersurfaceModel_of_forall_isSeparable.solution
