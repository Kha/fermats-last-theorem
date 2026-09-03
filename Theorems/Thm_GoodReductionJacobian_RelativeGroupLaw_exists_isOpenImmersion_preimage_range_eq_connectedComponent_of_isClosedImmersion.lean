import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_preimage_range_eq_connectedComponent_of_isClosedImmersion

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_preimage_range_eq_connectedComponent_of_isClosedImmersion
    {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
    [LocallyOfFiniteType g] [QuasiCompact g] (LB : RelativeGroupLaw R g)
    {K : Type u} [Field K] (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    [IsClosedImmersion ι] :
    ∃ (U : Scheme.{u}) (i : U ⟶ B) (LU : RelativeGroupLaw R (i ≫ g)),
      IsOpenImmersion i ∧
      Set.range i =
        (pullback.fst g ι ''
          (connectedComponent
            (((LB.baseChange ι).one (𝟙 (Spec (CommRingCat.of K)))).1
              (IsLocalRing.closedPoint K)))ᶜ)ᶜ ∧
      pullback.fst g ι ⁻¹' Set.range i =
        connectedComponent
          (((LB.baseChange ι).one (𝟙 (Spec (CommRingCat.of K)))).1 (IsLocalRing.closedPoint K)) ∧
      (Set.range (pullback.fst g ι))ᶜ ⊆ Set.range i ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ g)),
        NeronModelInfra.schemeHomOverComp (LU.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ g) g) =
          LB.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ g) g))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ g) g))) ∧
      (LB.IsCommutative → LU.IsCommutative) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_preimage_range_eq_connectedComponent_of_isClosedImmersion.solution
