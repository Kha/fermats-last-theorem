import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_faithfullyFlat_isAdicComplete_irreducible

set_option autoImplicit false

universe u

theorem IsDiscreteValuationRing.exists_faithfullyFlat_isAdicComplete_irreducible
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (p : ℕ) (hunif : Irreducible (p : R)) :
    ∃ (R₁ : Type u) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsDiscreteValuationRing R₁) (_ : CharZero R₁)
      (_ : Algebra R R₁) (_ : Module.FaithfullyFlat R R₁),
      IsAdicComplete (IsLocalRing.maximalIdeal R₁) R₁ ∧ Irreducible (p : R₁) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_faithfullyFlat_isAdicComplete_irreducible.solution
