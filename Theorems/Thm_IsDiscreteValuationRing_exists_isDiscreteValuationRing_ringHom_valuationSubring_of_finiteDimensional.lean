import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_isDiscreteValuationRing_ringHom_valuationSubring_of_finiteDimensional

set_option autoImplicit false

open IsLocalRing

theorem IsDiscreteValuationRing.exists_isDiscreteValuationRing_ringHom_valuationSubring_of_finiteDimensional
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (F : Type) [Field F] [Algebra O F] [IsFractionRing O F]
    {L : Type} [Field L] (A : ValuationSubring L) (K' : Subfield L)
    [Algebra O K'] [Algebra F K'] [IsScalarTower O F K'] [FiniteDimensional F K'] [Algebra.IsSeparable F K']
    (ιA : O →+* A) [IsLocalHom ιA] (hιA : ∀ x : O, ((ιA x : A) : L) = ((algebraMap O K' x : K') : L)) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (σ : O →+* O') (ι' : O' →+* A) (j' : O' →+* K'),
      Function.Injective ι' ∧ IsLocalHom ι' ∧ ι'.comp σ = ιA ∧
      (∀ x : O', ((ι' x : A) : L) = ((j' x : K') : L)) ∧ j'.comp σ = algebraMap O K' ∧
      (∀ c : K', ∃ a b : O', j' b ≠ 0 ∧ c * j' b = j' a) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_isDiscreteValuationRing_ringHom_valuationSubring_of_finiteDimensional.solution
