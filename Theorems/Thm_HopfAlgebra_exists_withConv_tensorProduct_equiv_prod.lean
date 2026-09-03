import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_withConv_tensorProduct_equiv_prod

open scoped TensorProduct
theorem HopfAlgebra.exists_withConv_tensorProduct_equiv_prod
    {R : Type} [CommRing R] {Γ : Type} [Group Γ]
    (H₁ H₂ : Type) [CommRing H₁] [CommRing H₂] [HopfAlgebra R H₁] [HopfAlgebra R H₂]
    {L : Type} [CommRing L] [Algebra R L] [MulSemiringAction Γ L] [SMulCommClass Γ R L] :
    ∃ e : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] L) ≃ WithConv (H₁ →ₐ[R] L) × WithConv (H₂ →ₐ[R] L),
      (∀ f g, e (f * g) = e f * e g) ∧
      ∀ (σ : Γ) (f g : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] L)),
        (∀ x : H₁ ⊗[R] H₂, g x = σ • (f x)) →
          (∀ y : H₁, (e g).1 y = σ • ((e f).1 y)) ∧ (∀ z : H₂, (e g).2 z = σ • ((e f).2 z)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_withConv_tensorProduct_equiv_prod.solution
