import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_completeOrthogonalIdempotents_zmod_of_natCard_algHom_eq_of_ne_two

theorem HopfAlgebra.exists_completeOrthogonalIdempotents_zmod_of_natCard_algHom_eq_of_ne_two
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K) (_ : Algebra.FiniteType ℤ K)
    (_ : Module.Flat ℤ K)
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ)
      (k : K), σ (ψ k) = ψ k) :
    ∃ e : ZMod q → K,
      CompleteOrthogonalIdempotents e ∧
      (∀ (T : Type) [CommRing T] (φ ψ : K →ₐ[ℤ] T) (c : ZMod q),
        (WithConv.toConv φ * WithConv.toConv ψ) (e c) = ∑ a, φ (e a) * ψ (e (c - a))) ∧
      (∀ (T : Type) [CommRing T] (a : ZMod q),
        (1 : WithConv (K →ₐ[ℤ] T)) (e a) = if a = 0 then 1 else 0) ∧
      ((∀ (T : Type) [CommRing T] (b : ZMod q → T), CompleteOrthogonalIdempotents b →
          ∃! φ : K →ₐ[ℤ] T, ∀ a, φ (e a) = b a) ∨
       ((∀ a, a ≠ 0 → ∃ u : K, u * (p * e a) = e a) ∧
        (∀ (T : Type) [CommRing T] (b : ZMod q → T), CompleteOrthogonalIdempotents b →
          (∀ a, a ≠ 0 → ∃ v : T, v * (p * b a) = b a) →
          ∃! φ : K →ₐ[ℤ] T, ∀ a, φ (e a) = b a))) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_completeOrthogonalIdempotents_zmod_of_natCard_algHom_eq_of_ne_two.solution
