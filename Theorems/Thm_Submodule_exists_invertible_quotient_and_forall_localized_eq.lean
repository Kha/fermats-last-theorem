import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_exists_invertible_quotient_and_forall_localized_eq

set_option autoImplicit false

open scoped TensorProduct

theorem Submodule.exists_invertible_quotient_and_forall_localized_eq
    {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] [Module.FinitePresentation R V]
    (Vₚ : PrimeSpectrum R → Type) [∀ x, AddCommGroup (Vₚ x)] [∀ x, Module R (Vₚ x)]
    [∀ x, Module (Localization.AtPrime x.asIdeal) (Vₚ x)]
    [∀ x, IsScalarTower R (Localization.AtPrime x.asIdeal) (Vₚ x)]
    (f : ∀ x, V →ₗ[R] Vₚ x) [∀ x, IsLocalizedModule x.asIdeal.primeCompl (f x)]
    (Λ : ∀ x, Submodule (Localization.AtPrime x.asIdeal) (Vₚ x))
    (hinv : ∀ x, Module.Invertible (Localization.AtPrime x.asIdeal) (Vₚ x ⧸ Λ x))
    (hloc : ∀ x : PrimeSpectrum R, ∃ r : R, r ∉ x.asIdeal ∧ ∃ N : Submodule R V, N.FG ∧
      ∀ y : PrimeSpectrum R, r ∉ y.asIdeal →
        Submodule.localized' (Localization.AtPrime y.asIdeal) y.asIdeal.primeCompl (f y) N = Λ y) :
    ∃ N : Submodule R V, Module.Invertible R (V ⧸ N) ∧
      ∀ x : PrimeSpectrum R, Submodule.localized' (Localization.AtPrime x.asIdeal) x.asIdeal.primeCompl (f x) N = Λ x := by p2m_exact_reverting @_root_.P2MW.S_Submodule_exists_invertible_quotient_and_forall_localized_eq.solution
