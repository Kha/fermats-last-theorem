import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_cocycle_trans_symm_of_comparison_identities

set_option autoImplicit false

universe u

open TensorProduct Algebra.TensorProduct

theorem Algebra.TensorProduct.cocycle_trans_symm_of_comparison_identities
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    (R' : Type u) [CommRing R'] [Algebra S R']
    (R'' : Type u) [CommRing R''] [Algebra (S' ⊗[S] S') R''] [Algebra S R''] [IsScalarTower S (S' ⊗[S] S') R'']
    (R''' : Type u) [CommRing R'''] [Algebra (S' ⊗[S] (S' ⊗[S] S')) R'''] [Algebra S R'''] [IsScalarTower S (S' ⊗[S] (S' ⊗[S] S')) R''']
    (ϑ₁ ϑ₂ : R' →ₐ[S] R'')
    (β₁ : R' ⊗[S] S' ≃ₐ[S] R'')
    (hβ₁ : ∀ (r : R') (t : S'), β₁ (r ⊗ₜ t) = ϑ₁ r * algebraMap (S' ⊗[S] S') R'' (1 ⊗ₜ t))
    (β₂ : S' ⊗[S] R' ≃ₐ[S] R'')
    (hβ₂ : ∀ (s : S') (r : R'), β₂ (s ⊗ₜ r) = algebraMap (S' ⊗[S] S') R'' (s ⊗ₜ 1) * ϑ₂ r)
    (σ₁₂ σ₁₃ σ₂₃ : R'' →ₐ[S] R''')
    (hσ₁₂ : σ₁₂.comp (IsScalarTower.toAlgHom S (S' ⊗[S] S') R'') =
      ((IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp
        (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S'))))
    (hσ₁₃ : σ₁₃.comp (IsScalarTower.toAlgHom S (S' ⊗[S] S') R'') =
      ((IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp
        (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S'))))
    (hσ₂₃ : σ₂₃.comp (IsScalarTower.toAlgHom S (S' ⊗[S] S') R'') =
      ((IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp
        (Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S'))))
    (hA : ∀ x : R', σ₁₃ (ϑ₁ x) = σ₁₂ (ϑ₁ x)) (hB : ∀ x : R', σ₂₃ (ϑ₁ x) = σ₁₂ (ϑ₂ x))
    (hC : ∀ x : R', σ₂₃ (ϑ₂ x) = σ₁₃ (ϑ₂ x))
    (hbij : Function.Bijective
      (Algebra.TensorProduct.lift (σ₁₂.comp ϑ₁)
        ((IsScalarTower.toAlgHom S (S' ⊗[S] (S' ⊗[S] S')) R''').comp
          (Algebra.TensorProduct.includeRight (R := S) (A := S') (B := S' ⊗[S] S')))
        (fun _ _ => Commute.all _ _) : R' ⊗[S] (S' ⊗[S] S') →ₐ[S] R''')) :
    let φ : R' ⊗[S] S' ≃ₐ[S] S' ⊗[S] R' := β₁.trans β₂.symm
    (Algebra.TensorProduct.map (AlgHom.id S S') φ.toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' R' S').toAlgHom.comp
          (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S'))) =
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.comm S R' S').toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' R' S').toAlgHom.comp
          ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S')).comp
            ((Algebra.TensorProduct.assoc S S S R' S' S').symm.toAlgHom.comp
              ((Algebra.TensorProduct.map (AlgHom.id S R') (Algebra.TensorProduct.comm S S' S').toAlgHom).comp
                (Algebra.TensorProduct.assoc S S S R' S' S').toAlgHom)))) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_cocycle_trans_symm_of_comparison_identities.solution
