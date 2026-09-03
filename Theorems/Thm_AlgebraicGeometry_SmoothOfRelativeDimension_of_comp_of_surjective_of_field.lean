import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_of_surjective_of_field

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_of_surjective_of_field
    {k : Type u} [Field k] {G Q : Scheme.{u}} [Nonempty G] (fQ : Q ⟶ Spec (CommRingCat.of k)) (q : G ⟶ Q)
    (g h : ℕ) [SmoothOfRelativeDimension g (q ≫ fQ)] [SmoothOfRelativeDimension h q] [Surjective q]
    [QuasiCompact q] : SmoothOfRelativeDimension (g - h) fQ ∧ h ≤ g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_of_surjective_of_field.solution
