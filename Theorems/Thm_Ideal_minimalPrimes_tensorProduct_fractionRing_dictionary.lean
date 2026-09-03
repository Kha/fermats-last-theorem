import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_minimalPrimes_tensorProduct_fractionRing_dictionary

set_option autoImplicit false
open scoped TensorProduct

theorem Ideal.minimalPrimes_tensorProduct_fractionRing_dictionary
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (j₀ : B)
    [IsDomain ↥(Algebra.adjoin A ({j₀} : Set B))]
    (hint : Algebra.IsIntegral ↥(Algebra.adjoin A ({j₀} : Set B)) B)
    (hdom : ∀ 𝔭 ∈ (⊥ : Ideal B).minimalPrimes,
      Ideal.comap (algebraMap ↥(Algebra.adjoin A ({j₀} : Set B)) B) 𝔭 = ⊥) :
    letI S := ↥(Algebra.adjoin A ({j₀} : Set B))
    letI F := FractionRing S
    letI R := F ⊗[S] B
    letI ιR : B →ₐ[S] R := Algebra.TensorProduct.includeRight
    (∀ 𝔓 : Ideal R, 𝔓.IsPrime → Ideal.comap ιR 𝔓 ∈ (⊥ : Ideal B).minimalPrimes) ∧
    (∀ 𝔭 ∈ (⊥ : Ideal B).minimalPrimes, ∃! 𝔓 : Ideal R, 𝔓.IsPrime ∧ Ideal.comap ιR 𝔓 = 𝔭) ∧
    (∀ e : B ≃ₐ[A] B, e j₀ = j₀ →
      ∃ ee : R ≃ₐ[F] R, ∀ b : B, ee (ιR b) = ιR (e b)) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_minimalPrimes_tensorProduct_fractionRing_dictionary.solution
