import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat

theorem HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat
    (q : ℕ) [Fact q.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A] [Module.Finite ℚ A]
    (hgenq : Nat.card (A →ₐ[ℚ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : A →ₐ[ℚ] AlgebraicClosure ℚ) (a : A),
        σ (ψ a) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) a) :
    Nonempty (A ≃ₐc[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod q))) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat.solution
