import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_withConv_equiv_padic_of_withConv_equiv_algebraicClosure

set_option autoImplicit false
theorem HopfAlgebra.exists_withConv_equiv_padic_of_withConv_equiv_algebraicClosure
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A] (hAfin : Module.Finite ℚ A)
    {N : Type} [AddCommGroup N] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (eA : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ) ≃ N)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ)),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f)) :
    ∃ eAp : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p]) ≃ N,
      (∀ f g, eAp (f * g) = eAp f + eAp g) ∧
      ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p])),
        (∀ a : A, g a = σ (f a)) → eAp g = (localGaloisToGlobal p σ) • (eAp f) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_withConv_equiv_padic_of_withConv_equiv_algebraicClosure.solution
