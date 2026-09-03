import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_exists_isGalois_compositum

set_option autoImplicit false

theorem NumberField.exists_isGalois_compositum
    (E F L : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra E F] [Algebra E L] [IsGalois E F] [IsGalois E L] :
    ∃ (N : Type) (_ : Field N) (_ : NumberField N) (_ : Algebra E N) (_ : Algebra F N) (_ : Algebra L N)
      (_ : IsScalarTower E F N) (_ : IsScalarTower E L N),
      IsGalois E N ∧
      ∀ σ : N ≃ₐ[E] N, (∀ x : F, σ (algebraMap F N x) = algebraMap F N x) →
        (∀ y : L, σ (algebraMap L N y) = algebraMap L N y) → σ = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_isGalois_compositum.solution
