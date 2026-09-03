import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_polynomial_isUnit_aeval_imp_etale_levelSet

universe u

open scoped TensorProduct
open Polynomial

theorem Algebra.exists_polynomial_isUnit_aeval_imp_etale_levelSet
    (R : Type u) [CommRing R] [IsLocalRing R]
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    [IsDomain (IsLocalRing.ResidueField R ⊗[R] A)]
    (f : A) (m : ℕ) (hm : IsUnit (m : R))
    (hls : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
        Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
        Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
        Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) = m) :
    ∃ D : Polynomial R, (∃ i, IsUnit (D.coeff i)) ∧
      ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] (s : S),
        IsUnit (Polynomial.aeval s D) →
        Algebra.Etale S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_polynomial_isUnit_aeval_imp_etale_levelSet.solution
