import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_algEquiv_comul_of_withConv_equiv_algClosure_padic

open scoped TensorProduct in
theorem HopfAlgebra.exists_algEquiv_comul_of_withConv_equiv_algClosure_padic
    (p : ℕ) [Fact p.Prime]
    {M : Type} [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M]
    (A : Type) [CommRing A] [HopfAlgebra ℚ_[p] A]
    (hAfin : Module.Finite ℚ_[p] A) (hAcocomm : Coalgebra.IsCocomm ℚ_[p] A)
    (eA : WithConv (A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) ≃ M)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f))
    (B : Type) [CommRing B] [HopfAlgebra ℚ_[p] B]
    (hBfin : Module.Finite ℚ_[p] B) (hBcocomm : Coalgebra.IsCocomm ℚ_[p] B)
    (eB : WithConv (B →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) ≃ M)
    (heB_add : ∀ f g, eB (f * g) = eB f + eB g)
    (heB_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (B →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ b : B, g b = σ (f b)) → eB g = σ • (eB f)) :
    ∃ φ : B ≃ₐ[ℚ_[p]] A,
      ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_algEquiv_comul_of_withConv_equiv_algClosure_padic.solution
