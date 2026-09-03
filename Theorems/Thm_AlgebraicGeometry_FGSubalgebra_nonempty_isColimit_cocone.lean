import Definitions.Def_AlgebraicGeometry_FGSubalgebra
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_FGSubalgebra_nonempty_isColimit_cocone

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.FGSubalgebra.nonempty_isColimit_cocone
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    Nonempty (IsColimit (FGSubalgebra.cocone R A)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_FGSubalgebra_nonempty_isColimit_cocone.solution
