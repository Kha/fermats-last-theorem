import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_GoodReductionJacobian_NsmulEigenSubdatum
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_nonempty_iso_tensorUnit_of_hom_eigenSubdatum_one_of_bijective_smul_eigenOne

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.nonempty_iso_tensorUnit_of_hom_eigenSubdatum_one_of_bijective_smul_eigenOne
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ)
    (hG : ∀ x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n, L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n)
    (N : A.Modules)
    (φ : OModulePresheaf.Hom (OModulePresheaf.ofModules f N) (L.eigenSubdatum n hG 1))
    (ψ : OModulePresheaf.Hom (L.eigenSubdatum n hG 1) (OModulePresheaf.ofModules f N))
    (h : ∀ (U : A.Opens) (s : (L.eigenSubdatum n hG 1).obj U), φ.app U (ψ.app U s) = s)
    (h' : ∀ (U : A.Opens) (s : (OModulePresheaf.ofModules f N).obj U), ψ.app U (φ.app U s) = s)
    (hone : ∀ U : A.affineOpens, Function.Bijective (fun a : Γ(A, U.1) => a • L.eigenOne n hG U.1)) :
    Nonempty (N ≅ 𝟙_ (A.Modules)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nonempty_iso_tensorUnit_of_hom_eigenSubdatum_one_of_bijective_smul_eigenOne.solution
