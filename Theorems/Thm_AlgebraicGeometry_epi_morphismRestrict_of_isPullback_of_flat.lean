import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_epi_morphismRestrict_of_isPullback_of_flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
theorem AlgebraicGeometry.epi_morphismRestrict_of_isPullback_of_flat
    {X Y X' Y' : Scheme.{0}} (p : X ⟶ Y) [IsAffineHom p] [Surjective p]
    (f : Y' ⟶ Y) [Flat f] (p' : X' ⟶ Y') (q : X' ⟶ X) (sq : IsPullback q p' p f)
    (hp : ∀ U : Y.Opens, Epi (p ∣_ U)) (U' : Y'.Opens) : Epi (p' ∣_ U') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_epi_morphismRestrict_of_isPullback_of_flat.solution
