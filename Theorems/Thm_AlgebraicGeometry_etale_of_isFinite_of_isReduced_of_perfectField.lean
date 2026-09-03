import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_etale_of_isFinite_of_isReduced_of_perfectField

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.etale_of_isFinite_of_isReduced_of_perfectField
    {K : Type u} [Field K] [PerfectField K]
    {B : Scheme.{u}} (g : B ⟶ Spec (CommRingCat.of K)) [IsFinite g] [IsReduced B] : Etale g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_etale_of_isFinite_of_isReduced_of_perfectField.solution
