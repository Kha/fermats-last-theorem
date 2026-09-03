import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_algEquiv_baseChange_padic_comul_of_withConv_equiv

open scoped NNReal TensorProduct
theorem HopfAlgebra.exists_algEquiv_baseChange_padic_comul_of_withConv_equiv
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A]
    (hAfin : Module.Finite ℚ A) (hAcocomm : Coalgebra.IsCocomm ℚ A)
    (Hp : Type) [CommRing Hp] [HopfAlgebra ℤ_[p] Hp]
    (hfin : Module.Finite ℤ_[p] Hp) (hflat : Module.Flat ℤ_[p] Hp)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] Hp)
    {M : Type} [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M]
    (eHp : WithConv (Hp →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ M)
    (heHp_add : ∀ f g, eHp (f * g) = eHp f + eHp g)
    (heHp_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (Hp →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ x : Hp, g x = σ (f x)) → eHp g = σ • (eHp f))
    (eAp : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p]) ≃ M)
    (heAp_add : ∀ f g, eAp (f * g) = eAp f + eAp g)
    (heAp_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p])),
      (∀ a : A, g a = σ (f a)) → eAp g = σ • (eAp f)) :
    ∃ φ : (ℚ_[p] ⊗[ℚ] A) ≃ₐ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] Hp),
      ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_algEquiv_baseChange_padic_comul_of_withConv_equiv.solution
