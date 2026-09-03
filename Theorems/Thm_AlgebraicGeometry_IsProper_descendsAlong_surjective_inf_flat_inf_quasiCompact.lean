import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsProper_descendsAlong_surjective_inf_flat_inf_quasiCompact

universe u

open CategoryTheory MorphismProperty AlgebraicGeometry

theorem AlgebraicGeometry.IsProper.descendsAlong_surjective_inf_flat_inf_quasiCompact :
    DescendsAlong (@IsProper : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsProper_descendsAlong_surjective_inf_flat_inf_quasiCompact.solution
