import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_of_finite_setOf_schemeHomOverComp_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_of_finite_setOf_schemeHomOverComp_eq_one
    {R : Type u} [CommRing R] {G H : Scheme.{u}}
    {gG : G ⟶ Spec (CommRingCat.of R)} {gH : H ⟶ Spec (CommRingCat.of R)}
    [LocallyOfFiniteType gG]
    (LG : RelativeGroupLaw R gG) (LH : RelativeGroupLaw R gH)
    (u : SchemeHomOver gG gH)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t gG),
      NeronModelInfra.schemeHomOverComp (LG.mul t x y) u =
        LH.mul t (NeronModelInfra.schemeHomOverComp x u)
          (NeronModelInfra.schemeHomOverComp y u))
    (hfin : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)),
      {x : SchemeHomOver t gG | NeronModelInfra.schemeHomOverComp x u = LH.one t}.Finite) :
    LocallyQuasiFinite u.1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_of_finite_setOf_schemeHomOverComp_eq_one.solution
