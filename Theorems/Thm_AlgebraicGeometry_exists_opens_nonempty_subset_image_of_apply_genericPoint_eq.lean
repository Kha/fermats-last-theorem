import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_opens_nonempty_subset_image_of_apply_genericPoint_eq

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Topology

universe u

theorem AlgebraicGeometry.exists_opens_nonempty_subset_image_of_apply_genericPoint_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [QuasiCompact f]
    [CompactSpace ↥Y] [QuasiSeparatedSpace ↥Y] [IrreducibleSpace ↥X] [IrreducibleSpace ↥Y]
    (hdom : f.base (genericPoint ↥X) = genericPoint ↥Y)
    (U : X.Opens) (hU : (U : Set ↥X).Nonempty) :
    ∃ V : Y.Opens, (V : Set ↥Y).Nonempty ∧ (V : Set ↥Y) ⊆ f.base '' (U : Set ↥X) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_opens_nonempty_subset_image_of_apply_genericPoint_eq.solution
