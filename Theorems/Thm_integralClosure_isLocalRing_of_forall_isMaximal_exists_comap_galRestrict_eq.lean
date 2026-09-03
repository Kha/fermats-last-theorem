import Mathlib
import P2M.Util
import P2M.Sol.S_integralClosure_isLocalRing_of_forall_isMaximal_exists_comap_galRestrict_eq

set_option autoImplicit false
theorem integralClosure.isLocalRing_of_forall_isMaximal_exists_comap_galRestrict_eq
    {R F L : Type*} [CommRing R] [IsDomain R] [Field F] [Field L]
    [Algebra R F] [IsFractionRing R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
    [FiniteDimensional F L]
    (htrans : ∀ M₁ M₂ : Ideal ↥(integralClosure R L), M₁.IsMaximal → M₂.IsMaximal →
      ∃ σ : L ≃ₐ[F] L, M₂ = Ideal.comap (galRestrict R F L ↥(integralClosure R L) σ) M₁) :
    IsLocalRing ↥(integralClosure R F) := by p2m_exact_reverting @_root_.P2MW.S_integralClosure_isLocalRing_of_forall_isMaximal_exists_comap_galRestrict_eq.solution
