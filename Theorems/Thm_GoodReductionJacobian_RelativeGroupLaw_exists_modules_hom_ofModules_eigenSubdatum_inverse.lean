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
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_modules_hom_ofModules_eigenSubdatum_inverse

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_modules_hom_ofModules_eigenSubdatum_inverse
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ)
    (hG : ∀ x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n, L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n)
    (χ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f → R) :
    ∃ (N : A.Modules) (φ : OModulePresheaf.Hom (OModulePresheaf.ofModules f N) (L.eigenSubdatum n hG χ))
      (ψ : OModulePresheaf.Hom (L.eigenSubdatum n hG χ) (OModulePresheaf.ofModules f N)),
      (∀ (U : A.Opens) (s : (L.eigenSubdatum n hG χ).obj U), φ.app U (ψ.app U s) = s) ∧
      (∀ (U : A.Opens) (s : (OModulePresheaf.ofModules f N).obj U), ψ.app U (φ.app U s) = s) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_modules_hom_ofModules_eigenSubdatum_inverse.solution
