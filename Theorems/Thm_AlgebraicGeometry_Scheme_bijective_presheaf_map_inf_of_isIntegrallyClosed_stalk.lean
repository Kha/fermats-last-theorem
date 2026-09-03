import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk"

theorem AlgebraicGeometry.Scheme.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk
    {X : Scheme.{u}} [IsLocallyNoetherian X] (V U : X.Opens)
    (hV : ∀ x : X, x ∈ V → IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (hU : ∀ x : X, x ∈ V → ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ U) :
    Function.Bijective (X.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk.solution
