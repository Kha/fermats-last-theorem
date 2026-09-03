import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_nonempty_and_subsingleton_rigidifiedIso_of_locIsoOnBase_of_forall_bijective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Polarisation
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.Polarisation.nonempty_and_subsingleton_rigidifiedIso_of_locIsoOnBase_of_forall_bijective
    {T : Type u} [CommRing T] {B : Scheme.{u}} (h : B ⟶ Spec (CommRingCat.of T)) [QuasiCompact h] [QuasiSeparated h]
    (hH0 : ∀ (T' : Type u) [CommRing T'] [Algebra T T'],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd h (Scheme.TwoAffineOpenCover.specMap T T')) ⊤
      Function.Bijective (algebraMap T' Γ(pullback h (Scheme.TwoAffineOpenCover.specMap T T'), ⊤)))
    (e : Spec (CommRingCat.of T) ⟶ B) (he : e ≫ h = 𝟙 _)
    (M M' : B.Modules) (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M')
    (hloc : LocIsoOnBase h M M')
    (α : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of T)).ringCatSheaf)
    (α' : (Scheme.Modules.pullback e).obj M' ≅ SheafOfModules.unit (Spec (CommRingCat.of T)).ringCatSheaf) :
    Nonempty {φ : M ≅ M' // (Scheme.Modules.pullback e).mapIso φ ≪≫ α' = α} ∧
      Subsingleton {φ : M ≅ M' // (Scheme.Modules.pullback e).mapIso φ ≪≫ α' = α} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_nonempty_and_subsingleton_rigidifiedIso_of_locIsoOnBase_of_forall_bijective.solution
