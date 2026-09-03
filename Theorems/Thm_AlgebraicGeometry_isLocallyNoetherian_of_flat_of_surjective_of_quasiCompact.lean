import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isLocallyNoetherian_of_flat_of_surjective_of_quasiCompact

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isLocallyNoetherian_of_flat_of_surjective_of_quasiCompact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [QuasiCompact f] [IsLocallyNoetherian X] :
    IsLocallyNoetherian Y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isLocallyNoetherian_of_flat_of_surjective_of_quasiCompact.solution
