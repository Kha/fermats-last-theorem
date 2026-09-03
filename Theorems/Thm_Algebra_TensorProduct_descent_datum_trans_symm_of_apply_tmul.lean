import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_descent_datum_trans_symm_of_apply_tmul

set_option autoImplicit false

universe u

open TensorProduct Algebra.TensorProduct

theorem Algebra.TensorProduct.descent_datum_trans_symm_of_apply_tmul
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    (A' : Type u) [CommRing A'] [Algebra S A'] [Algebra S' A'] [IsScalarTower S S' A']
    (𝒜' : ℕ → Submodule S' A')
    (A'' : Type u) [CommRing A''] [Algebra (S' ⊗[S] S') A''] [Algebra S A''] [IsScalarTower S (S' ⊗[S] S') A'']
    (𝒜'' : ℕ → Submodule (S' ⊗[S] S') A'')
    (ϑ₁ ϑ₂ : A' →ₐ[S] A'')
    (hϑ₁lin : ∀ (s : S') (a : A'), ϑ₁ (s • a) = algebraMap (S' ⊗[S] S') A'' (s ⊗ₜ 1) * ϑ₁ a)
    (hϑ₂lin : ∀ (s : S') (a : A'), ϑ₂ (s • a) = algebraMap (S' ⊗[S] S') A'' (1 ⊗ₜ s) * ϑ₂ a)
    (hϑ₁deg : ∀ n, ∀ a ∈ 𝒜' n, ϑ₁ a ∈ 𝒜'' n)
    (hspan₂ : ∀ n, 𝒜'' n ≤ Submodule.span (S' ⊗[S] S') (ϑ₂ '' (𝒜' n : Set A')))
    (β₁ : A' ⊗[S] S' ≃ₐ[S] A'')
    (hβ₁ : ∀ (a : A') (t : S'), β₁ (a ⊗ₜ t) = ϑ₁ a * algebraMap (S' ⊗[S] S') A'' (1 ⊗ₜ t))
    (β₂ : S' ⊗[S] A' ≃ₐ[S] A'')
    (hβ₂ : ∀ (s : S') (a : A'), β₂ (s ⊗ₜ a) = algebraMap (S' ⊗[S] S') A'' (s ⊗ₜ 1) * ϑ₂ a) :
    let φ : A' ⊗[S] S' ≃ₐ[S] S' ⊗[S] A' := β₁.trans β₂.symm
    φ.toAlgHom.comp (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S S' A') (AlgHom.id S S')) =
        Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom S S' A') ∧
      (∀ (n : ℕ) (a : A'), a ∈ 𝒜' n → ∀ t : S', φ (a ⊗ₜ t) ∈ ((𝒜' n).restrictScalars S).baseChange S') ∧
      (∀ a : A',
        a ∈ AlgHom.equalizer (φ.toAlgHom.comp (Algebra.TensorProduct.includeLeft : A' →ₐ[S] A' ⊗[S] S'))
              (Algebra.TensorProduct.includeRight : A' →ₐ[S] S' ⊗[S] A') ↔
          ϑ₁ a = ϑ₂ a) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_descent_datum_trans_symm_of_apply_tmul.solution
