import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_nonempty_splitting_of_isZero_H1_ihom
attribute [-simp] Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk Rep.coe_tateδneg2_apply

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.nonempty_splitting_of_isZero_H1_ihom {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) [Module.Free k X.X₃]
    (h : CategoryTheory.Limits.IsZero (groupCohomology ((ihom X.X₃).obj X.X₁) 1)) :
    Nonempty X.Splitting := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_splitting_of_isZero_H1_ihom.solution
