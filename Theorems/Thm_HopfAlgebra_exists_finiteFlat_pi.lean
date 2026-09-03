import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_finiteFlat_pi

theorem HopfAlgebra.exists_finiteFlat_pi {R L Γ ι : Type} [CommRing R] [CommRing L] [Algebra R L]
    [Finite ι] (π : Γ → L → L) (M : ι → Type) [∀ i, Add (M i)] (act : ∀ i, Γ → M i → M i)
    (h : ∀ i, ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ e : WithConv (H →ₐ[R] L) ≃ M i,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : Γ) (f g : WithConv (H →ₐ[R] L)), (∀ x, g x = π σ (f x)) → e g = act i σ (e f)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ e : WithConv (H →ₐ[R] L) ≃ (∀ i, M i),
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : Γ) (f g : WithConv (H →ₐ[R] L)), (∀ x, g x = π σ (f x)) →
          e g = fun i => act i σ (e f i) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_finiteFlat_pi.solution
