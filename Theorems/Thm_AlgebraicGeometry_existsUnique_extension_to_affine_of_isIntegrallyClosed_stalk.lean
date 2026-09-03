import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk
    {T Y : Scheme.{u}} [IsLocallyNoetherian T]
    (hT : ∀ x : T, IsDomain (T.presheaf.stalk x) ∧ IsIntegrallyClosed (T.presheaf.stalk x))
    [IsAffine Y] (V : T.Opens) (hV : ∀ x : T, ringKrullDim (T.presheaf.stalk x) ≤ 1 → x ∈ V)
    (v : (V : Scheme.{u}) ⟶ Y) :
    ∃! φ : T ⟶ Y, V.ι ≫ φ = v := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk.solution
