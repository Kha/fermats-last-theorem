import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_iso_of_iso

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem MumfordCongr.dualIso {X : Scheme.{0}} {𝓛 𝓛' : X.Modules} (e : 𝓛 ≅ 𝓛') :
    Nonempty (Scheme.Modules.dual 𝓛 ≅ Scheme.Modules.dual 𝓛') :=
  ⟨((MonoidalClosed.internalHom.mapIso e.op).app (𝟙_ X.Modules)).symm⟩

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {𝓛 𝓛' : A.Modules} (e : 𝓛 ≅ 𝓛') :
    Nonempty (mumfordBundle f L 𝓛 ≅ mumfordBundle f L 𝓛') := by
  obtain ⟨ed⟩ := MumfordCongr.dualIso e
  exact ⟨(Scheme.Modules.pullback (addMor f L)).mapIso e ⊗ᵢ
    ((Scheme.Modules.pullback (pullback.fst f f)).mapIso ed ⊗ᵢ (Scheme.Modules.pullback (pullback.snd f f)).mapIso ed)⟩
