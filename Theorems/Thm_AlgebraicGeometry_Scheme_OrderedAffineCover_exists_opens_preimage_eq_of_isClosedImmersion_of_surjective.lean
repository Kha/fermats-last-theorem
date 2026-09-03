import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_opens_preimage_eq_of_isClosedImmersion_of_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits open AlgebraicGeometry hiding isAffine_of_isClosedImmersion_of_surjective

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_opens_preimage_eq_of_isClosedImmersion_of_surjective
    {P' P : Scheme.{u}} (j : P' ⟶ P) [IsClosedImmersion j] [Surjective j] (𝒲 : P'.OrderedAffineCover) :
    ∃ (V : 𝒲.ι → P.Opens), (∀ w, IsAffineOpen (V w)) ∧ (⨆ w, V w = ⊤) ∧ (∀ w, j ⁻¹ᵁ (V w) = 𝒲.U w) ∧
      (∀ (U : P.Opens) (w : 𝒲.ι), 𝒲.U w ≤ j ⁻¹ᵁ U → V w ≤ U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_opens_preimage_eq_of_isClosedImmersion_of_surjective.solution
