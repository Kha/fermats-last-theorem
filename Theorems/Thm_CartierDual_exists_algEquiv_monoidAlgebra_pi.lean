import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_CartierDual_exists_algEquiv_monoidAlgebra_pi

theorem CartierDual.exists_algEquiv_monoidAlgebra_pi
    (R : Type*) [CommRing R] (Γ : Type*) [CommGroup Γ] [Fintype Γ] :
    ∃ e : CartierDual R (MonoidAlgebra R Γ) ≃ₐ[R] (Γ → R),
      (∀ (φ : CartierDual R (MonoidAlgebra R Γ)) (x : Γ), e φ x = φ (MonoidAlgebra.single x 1)) ∧
      (∀ (φ : CartierDual R (MonoidAlgebra R Γ)) (x y : Γ),
        TensorProduct.dualDistrib R (MonoidAlgebra R Γ) (MonoidAlgebra R Γ)
          (TensorProduct.map (CartierDual.toDual R (MonoidAlgebra R Γ)).toLinearMap
            (CartierDual.toDual R (MonoidAlgebra R Γ)).toLinearMap (Coalgebra.comul (R := R) φ))
          (MonoidAlgebra.single x 1 ⊗ₜ[R] MonoidAlgebra.single y 1) = φ (MonoidAlgebra.single (x * y) 1)) ∧
      (∀ φ : CartierDual R (MonoidAlgebra R Γ), Coalgebra.counit (R := R) φ = φ 1) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_exists_algEquiv_monoidAlgebra_pi.solution
