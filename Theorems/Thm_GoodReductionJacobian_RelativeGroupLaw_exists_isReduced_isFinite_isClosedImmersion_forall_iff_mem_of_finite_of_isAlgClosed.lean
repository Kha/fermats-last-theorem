import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isReduced_isFinite_isClosedImmersion_forall_iff_mem_of_finite_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isReduced_isFinite_isClosedImmersion_forall_iff_mem_of_finite_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated h] [LocallyOfFiniteType h]
    (L : RelativeGroupLaw k h)
    (Z : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h)) (hZ : Z.Finite)
    (hone : L.one _ ∈ Z)
    (hmul : ∀ x ∈ Z, ∀ y ∈ Z, L.mul _ x y ∈ Z)
    (hinv : ∀ x ∈ Z, L.inv _ x ∈ Z) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of k)) (LB : RelativeGroupLaw k g) (i : SchemeHomOver g h),
      IsReduced B ∧ IsFinite g ∧ IsClosedImmersion i.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
        NeronModelInfra.schemeHomOverComp (LB.mul t x y) i =
          L.mul t (NeronModelInfra.schemeHomOverComp x i) (NeronModelInfra.schemeHomOverComp y i)) ∧
      (∃ eB : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g ≃ ↥Z,
        ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g,
          ((eB y : ↥Z) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h) = NeronModelInfra.schemeHomOverComp y i) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isReduced_isFinite_isClosedImmersion_forall_iff_mem_of_finite_of_isAlgClosed.solution
