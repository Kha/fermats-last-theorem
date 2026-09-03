import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct

open scoped TensorProduct

universe v

theorem Deformation.DieudonneModule.exists_addEquiv_prod_apply_eq_map_of_tensorProduct
    (p : ℕ) [Fact p.Prime]
    (B₁ B₂ : Type v) [CommRing B₁] [CommRing B₂] [Bialgebra (ZMod p) B₁] [Bialgebra (ZMod p) B₂] :
    ∃ (i₁ : B₁ →ₐc[ZMod p] B₁ ⊗[ZMod p] B₂) (i₂ : B₂ →ₐc[ZMod p] B₁ ⊗[ZMod p] B₂)
      (q₁ : B₁ ⊗[ZMod p] B₂ →ₐc[ZMod p] B₁) (q₂ : B₁ ⊗[ZMod p] B₂ →ₐc[ZMod p] B₂),
      (i₁ : B₁ →ₐ[ZMod p] B₁ ⊗[ZMod p] B₂) = Algebra.TensorProduct.includeLeft ∧
      (i₂ : B₂ →ₐ[ZMod p] B₁ ⊗[ZMod p] B₂) = Algebra.TensorProduct.includeRight ∧
      (∀ x y, q₁ (x ⊗ₜ[ZMod p] y) = Coalgebra.counit (R := ZMod p) y • x) ∧
      (∀ x y, q₂ (x ⊗ₜ[ZMod p] y) = Coalgebra.counit (R := ZMod p) x • y) ∧
      ∃ e : Deformation.DieudonneModule (ZMod p) p (B₁ ⊗[ZMod p] B₂) ≃+
          Deformation.DieudonneModule (ZMod p) p B₁ × Deformation.DieudonneModule (ZMod p) p B₂,
        (∀ z, e z = (Deformation.DieudonneModule.map (ZMod p) p q₁ z,
          Deformation.DieudonneModule.map (ZMod p) p q₂ z)) ∧
        (∀ m₁ m₂, e.symm (m₁, m₂) = Deformation.DieudonneModule.map (ZMod p) p i₁ m₁ +
          Deformation.DieudonneModule.map (ZMod p) p i₂ m₂) ∧
        (∀ z, e (Deformation.DieudonneModule.frobenius (ZMod p) p (B₁ ⊗[ZMod p] B₂) z) =
          (Deformation.DieudonneModule.frobenius (ZMod p) p B₁ (e z).1,
            Deformation.DieudonneModule.frobenius (ZMod p) p B₂ (e z).2)) ∧
        (∀ z, e (Deformation.DieudonneModule.verschiebung (ZMod p) p (B₁ ⊗[ZMod p] B₂) z) =
          (Deformation.DieudonneModule.verschiebung (ZMod p) p B₁ (e z).1,
            Deformation.DieudonneModule.verschiebung (ZMod p) p B₂ (e z).2)) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct.solution
