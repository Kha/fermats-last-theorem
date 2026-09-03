import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial

universe u

open Polynomial
open scoped TensorProduct

theorem Algebra.levelSet_finite_free_finrank_of_flat_polynomial
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (f : A) (d : ℕ)
    (hfin : (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.Finite)
    (hflat : (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.Flat)
    (hrank : ∀ (L : Type u) [Field L] [Algebra R L] (x : L),
      Module.finrank L (L ⊗[R] A ⧸ Ideal.span {(1 : L) ⊗ₜ[R] f - x ⊗ₜ[R] (1 : A)}) = d) :
    ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
      Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
        Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
        Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) = d := by p2m_exact_reverting @_root_.P2MW.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial.solution
