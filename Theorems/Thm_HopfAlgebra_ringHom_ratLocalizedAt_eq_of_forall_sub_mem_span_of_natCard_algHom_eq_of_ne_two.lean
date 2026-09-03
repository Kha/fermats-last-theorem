import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_ringHom_ratLocalizedAt_eq_of_forall_sub_mem_span_of_natCard_algHom_eq_of_ne_two

theorem HopfAlgebra.ringHom_ratLocalizedAt_eq_of_forall_sub_mem_span_of_natCard_algHom_eq_of_ne_two
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K) (_ : Algebra.FiniteType ℤ K)
    (_ : Module.Flat ℤ K)
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ)
      (k : K), σ (ψ k) = ψ k)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (χ χ' : K →+* GaloisRep.ratLocalizedAt ℓ)
    (h : ∀ k : K, χ k - χ' k ∈ Ideal.span {(ℓ : GaloisRep.ratLocalizedAt ℓ)}) : χ = χ' := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_ringHom_ratLocalizedAt_eq_of_forall_sub_mem_span_of_natCard_algHom_eq_of_ne_two.solution
