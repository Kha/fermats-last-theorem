import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOver_pullback_unit_equiv_ker
attribute [-simp] GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_schemeHomOver_pullback_unit_equiv_ker
    {R : Type u} [CommRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (u : SchemeHomOver g f) :
    ∃ e : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        SchemeHomOver t (pullback.snd u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ≃
          {x : SchemeHomOver t g // NeronModelInfra.schemeHomOverComp x u = L.one t},
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (y : SchemeHomOver t (pullback.snd u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1)),
        ((e t y : {x : SchemeHomOver t g // _}) : SchemeHomOver t g).1 =
          y.1 ≫ pullback.fst u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOver_pullback_unit_equiv_ker.solution
