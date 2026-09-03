import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

theorem AlgebraicGeometry.closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top
    {S : Scheme.{u}} [IsAffine S] {A B : CommRingCat.{u}} (a : Spec A ⟶ S) (b : Spec B ⟶ S) :
    Subring.closure
      (Set.range (pullback.fst a b).appTop ∪ Set.range (pullback.snd a b).appTop) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top.solution
