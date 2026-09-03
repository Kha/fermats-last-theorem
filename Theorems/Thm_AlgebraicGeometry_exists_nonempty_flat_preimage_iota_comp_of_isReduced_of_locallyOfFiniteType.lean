import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_nonempty_flat_preimage_iota_comp_of_isReduced_of_locallyOfFiniteType

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_nonempty_flat_preimage_iota_comp_of_isReduced_of_locallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [IsReduced S] [Nonempty S]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ Flat ((f ⁻¹ᵁ U).ι ≫ f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_nonempty_flat_preimage_iota_comp_of_isReduced_of_locallyOfFiniteType.solution
