import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_nonempty_rigidifiedIso_of_iso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Polarisation
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.Polarisation.nonempty_rigidifiedIso_of_iso
    {T : Type u} [CommRing T] {B : Scheme.{u}} (h : B ⟶ Spec (CommRingCat.of T))
    (hΓ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of T)).inv ≫ h.appTop).hom)
    (e : Spec (CommRingCat.of T) ⟶ B) (he : e ≫ h = 𝟙 _)
    (M M' : B.Modules)
    (α : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of T)).ringCatSheaf)
    (α' : (Scheme.Modules.pullback e).obj M' ≅ SheafOfModules.unit (Spec (CommRingCat.of T)).ringCatSheaf)
    (φ₀ : M ≅ M') :
    Nonempty {φ : M ≅ M' // (Scheme.Modules.pullback e).mapIso φ ≪≫ α' = α} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_nonempty_rigidifiedIso_of_iso.solution
