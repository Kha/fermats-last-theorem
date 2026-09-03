import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_iff_and_kernelTrivial_iff_of_iso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_iff_and_kernelTrivial_iff_of_iso
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (𝓝 𝓝' : A.Modules) (e : 𝓝 ≅ 𝓝') :
    (KernelIsTwoTorsion f L 𝓝 ↔ KernelIsTwoTorsion f L 𝓝') ∧ (KernelTrivial f L 𝓝 ↔ KernelTrivial f L 𝓝') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_iff_and_kernelTrivial_iff_of_iso.solution
