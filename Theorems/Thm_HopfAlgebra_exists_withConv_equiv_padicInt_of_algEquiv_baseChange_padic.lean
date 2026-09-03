import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_withConv_equiv_padicInt_of_algEquiv_baseChange_padic

open scoped TensorProduct in
theorem HopfAlgebra.exists_withConv_equiv_padicInt_of_algEquiv_baseChange_padic
    (p : ℕ) [Fact p.Prime]
    {M : Type} [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M]
    (A : Type) [CommRing A] [HopfAlgebra ℚ_[p] A]
    (eA : WithConv (A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) ≃ M)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f))
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (φ : (ℚ_[p] ⊗[ℤ_[p]] H) ≃ₐ[ℚ_[p]] A)
    (hφcomul : ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x)) :
    ∃ e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ M,
      (∀ f g, e (f * g) = e f + e g) ∧
      ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
        (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
        (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_withConv_equiv_padicInt_of_algEquiv_baseChange_padic.solution
