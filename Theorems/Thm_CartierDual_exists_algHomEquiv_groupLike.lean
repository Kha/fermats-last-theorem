import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_CartierDual_exists_algHomEquiv_groupLike

universe u v w
theorem CartierDual.exists_algHomEquiv_groupLike
    (R : Type u) [CommRing R] (H : Type v) [CommRing H] [Bialgebra R H] [Module.Finite R H] [Module.Free R H] :
    ∃ e : (∀ (B : Type w) [CommRing B] [Algebra R B], (CartierDual R H →ₐ[R] B) ≃ GroupLike B (TensorProduct R B H)),
      (∀ (B : Type w) [CommRing B] [Algebra R B] (ψ : CartierDual R H →ₐ[R] B) (φ : CartierDual R H),
          TensorProduct.rid R B (LinearMap.lTensor B (CartierDual.toDual R H φ) (e B ψ).val) = ψ φ) ∧
      (∀ (B : Type w) [CommRing B] [Algebra R B] (ψ₀ : CartierDual R H →ₐ[R] B),
          (∀ φ, ψ₀ φ = algebraMap R B (φ 1)) → (e B ψ₀).val = 1) ∧
      (∀ (B : Type w) [CommRing B] [Algebra R B] (ψ₁ ψ₂ ψ₃ : CartierDual R H →ₐ[R] B),
          WithConv.toConv ψ₃.toLinearMap = WithConv.toConv ψ₁.toLinearMap * WithConv.toConv ψ₂.toLinearMap →
          (e B ψ₃).val = (e B ψ₁).val * (e B ψ₂).val) ∧
      (∀ (B B' : Type w) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (τ : B →ₐ[R] B')
          (ψ : CartierDual R H →ₐ[R] B),
          (e B' (τ.comp ψ)).val = Algebra.TensorProduct.map τ (AlgHom.id R H) (e B ψ).val) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_exists_algHomEquiv_groupLike.solution
