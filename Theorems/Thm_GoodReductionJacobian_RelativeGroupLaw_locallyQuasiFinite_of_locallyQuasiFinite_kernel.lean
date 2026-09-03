import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_of_locallyQuasiFinite_kernel

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_of_locallyQuasiFinite_kernel
    {R : Type u} [CommRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}
    (LB : RelativeGroupLaw R g) (L : RelativeGroupLaw R f) (u : SchemeHomOver g f)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LB.mul t x y) u =
        L.mul t (NeronModelInfra.schemeHomOverComp x u) (NeronModelInfra.schemeHomOverComp y u))
    [LocallyOfFiniteType g]
    [LocallyQuasiFinite (pullback.snd u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1)]
    [QuasiCompact (pullback.snd u.1 (L.one (𝟙 (Spec (CommRingCat.of R)))).1)] :
    LocallyQuasiFinite u.1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_of_locallyQuasiFinite_kernel.solution
