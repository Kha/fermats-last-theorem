import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_exists_faithfullyFlat_algHom_lift_family_of_forall_isArtinianRing_exists_algHom_lift

set_option autoImplicit false

open MvPolynomial IsLocalRing

theorem MvPolynomial.exists_faithfullyFlat_algHom_lift_family_of_forall_isArtinianRing_exists_algHom_lift
    (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] {n : ℕ}
    (I J : Ideal (MvPolynomial (Fin n) R)) (hIJ : I ≤ J) (hJ : J.IsMaximal)
    (hlift : ∀ (T' T : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
      (ℓ : ℕ) [Fact ℓ.Prime] [CharP (ResidueField T') ℓ]
      [CommRing T] [Nontrivial T] [Algebra R T'] [Algebra R T]
      (p : T' →ₐ[R] T), Function.Surjective p → RingHom.ker p.toRingHom * maximalIdeal T' = ⊥ →
      ∀ m : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] T,
        ∃ m' : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] T', p.comp m' = m) :
    ∃ (D : ℕ → Type) (_ : ∀ N, CommRing (D N)) (_ : ∀ N, Algebra R (D N))
      (_ : ∀ N, Algebra (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N))
      (_ : ∀ N, IsScalarTower R (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N))
      (_ : ∀ N, Module.FaithfullyFlat (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N))
      (σ : ∀ N, (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] D N),
      ∀ (N : ℕ) (f : MvPolynomial (Fin n) R),
        σ N (Ideal.Quotient.mk I f) -
            algebraMap (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N) (Ideal.Quotient.mk (J ^ N ⊔ J * I) f) ∈
          Ideal.map (algebraMap (MvPolynomial (Fin n) R ⧸ (J ^ N ⊔ J * I)) (D N))
            (Ideal.map (Ideal.Quotient.mk (J ^ N ⊔ J * I)) (J ^ N ⊔ I)) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_faithfullyFlat_algHom_lift_family_of_forall_isArtinianRing_exists_algHom_lift.solution
