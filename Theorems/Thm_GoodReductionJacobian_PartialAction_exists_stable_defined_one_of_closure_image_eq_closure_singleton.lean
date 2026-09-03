import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_PartialAction_exists_stable_defined_one_of_closure_image_eq_closure_singleton
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.PartialAction.exists_stable_defined_one_of_closure_image_eq_closure_singleton
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsProper p] [IsIntegral P]
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L)
    (hcod : ∀ z : ↥(pullback f p), ringKrullDim ((pullback f p).presheaf.stalk z) ≤ 1 → z ∈ a.dom)
    (w w' : P) (hw₁ : ringKrullDim (P.presheaf.stalk w) = 1)
    (hw'₁ : ringKrullDim (P.presheaf.stalk w') = 1)
    (hsw : closure (a.hom.base '' ((a.dom.ι ≫ pullback.snd f p).base ⁻¹' closure {w})) =
      closure {w'}) :
    ∃ P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p,
      topologicalKrullDim ↥(closure {w'}) + 1 ≤ topologicalKrullDim ↥P ∧
      a.Stable (closure {w'}) ∧
      P₀.1 (IsLocalRing.closedPoint k) ∈ closure {w'} ∧
      a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀ := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_PartialAction_exists_stable_defined_one_of_closure_image_eq_closure_singleton.solution
