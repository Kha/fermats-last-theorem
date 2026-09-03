import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_isPGroup_algEquiv_compositum_of_isPGroup

set_option autoImplicit false

theorem NumberField.isPGroup_algEquiv_compositum_of_isPGroup
    (E F L N : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field L] [NumberField L]
    [Field N] [NumberField N]
    [Algebra E F] [Algebra E L] [Algebra E N] [Algebra F N] [Algebra L N]
    [IsScalarTower E F N] [IsScalarTower E L N] [IsGalois E F] [IsGalois E L] [IsGalois E N]
    (p : ℕ) [Fact p.Prime] (hF : IsPGroup p (F ≃ₐ[E] F)) (hL : IsPGroup p (L ≃ₐ[E] L))
    (hgen : ∀ σ : N ≃ₐ[E] N, (∀ x : F, σ (algebraMap F N x) = algebraMap F N x) →
      (∀ y : L, σ (algebraMap L N y) = algebraMap L N y) → σ = 1) :
    IsPGroup p (N ≃ₐ[E] N) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_isPGroup_algEquiv_compositum_of_isPGroup.solution
