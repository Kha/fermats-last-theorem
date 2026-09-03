import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_pullback_snd_of_isClosedImmersion_of_nsmul_eq_one
attribute [-simp] GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_pullback_snd_of_isClosedImmersion_of_nsmul_eq_one
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] [IsLocalRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R'))
    {X : Scheme.{u}} (i : X ⟶ A) [IsClosedImmersion i]
    (htors : G.nsmul (i ≫ f) n ⟨i, rfl⟩ = G.one (i ≫ f)) :
    FormallyUnramified (pullback.snd (i ≫ f) ι) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_pullback_snd_of_isClosedImmersion_of_nsmul_eq_one.solution
