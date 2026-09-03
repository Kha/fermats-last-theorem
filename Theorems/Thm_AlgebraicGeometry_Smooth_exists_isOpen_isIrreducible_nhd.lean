import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_exists_isOpen_isIrreducible_nhd
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Smooth.exists_isOpen_isIrreducible_nhd
    {k : Type u} [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k)) [Smooth f] (y : ↥Y) :
    ∃ Ω : Y.Opens, y ∈ Ω ∧ IsIrreducible (Ω : Set ↥Y) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_exists_isOpen_isIrreducible_nhd.solution
