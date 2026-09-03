import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_ringHom_comp_eq_and_subtype_comp_eq_and_isLocalHom_of_isDiscreteValuationRing

set_option autoImplicit false

theorem ValuationSubring.exists_ringHom_comp_eq_and_subtype_comp_eq_and_isLocalHom_of_isDiscreteValuationRing
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    (ιA' : O' →+* ↥A) (hιA'inj : Function.Injective ιA') (hιA'loc : IsLocalHom ιA')
    (R : Type) [CommRing R] [IsLocalRing R] (σ : O' →+* R) (hσ : IsLocalHom σ)
    (L : Type) [Field L] (r : R →+* L)
    (e₀ : L →+* AlgebraicClosure ℚ) (he₀ : e₀.comp (r.comp σ) = A.subtype.comp ιA') :
    ∃ (τ : L →+* AlgebraicClosure ℚ) (χ : R →+* ↥A),
      τ.comp (r.comp σ) = A.subtype.comp ιA' ∧ A.subtype.comp χ = τ.comp r ∧ IsLocalHom χ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_ringHom_comp_eq_and_subtype_comp_eq_and_isLocalHom_of_isDiscreteValuationRing.solution
