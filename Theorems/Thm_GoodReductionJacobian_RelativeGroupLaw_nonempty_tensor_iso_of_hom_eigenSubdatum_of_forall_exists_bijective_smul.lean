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
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_nonempty_tensor_iso_of_hom_eigenSubdatum_of_forall_exists_bijective_smul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.nonempty_tensor_iso_of_hom_eigenSubdatum_of_forall_exists_bijective_smul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ)
    (hG : ∀ x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n, L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n)
    (χ ψ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f → R)
    (N₁ N₂ N₃ : A.Modules)
    (φ₁ : OModulePresheaf.Hom (OModulePresheaf.ofModules f N₁) (L.eigenSubdatum n hG χ))
    (ψ₁ : OModulePresheaf.Hom (L.eigenSubdatum n hG χ) (OModulePresheaf.ofModules f N₁))
    (h₁ : ∀ (U : A.Opens) (s : (L.eigenSubdatum n hG χ).obj U), φ₁.app U (ψ₁.app U s) = s)
    (h₁' : ∀ (U : A.Opens) (s : (OModulePresheaf.ofModules f N₁).obj U), ψ₁.app U (φ₁.app U s) = s)
    (φ₂ : OModulePresheaf.Hom (OModulePresheaf.ofModules f N₂) (L.eigenSubdatum n hG ψ))
    (ψ₂ : OModulePresheaf.Hom (L.eigenSubdatum n hG ψ) (OModulePresheaf.ofModules f N₂))
    (h₂ : ∀ (U : A.Opens) (s : (L.eigenSubdatum n hG ψ).obj U), φ₂.app U (ψ₂.app U s) = s)
    (h₂' : ∀ (U : A.Opens) (s : (OModulePresheaf.ofModules f N₂).obj U), ψ₂.app U (φ₂.app U s) = s)
    (φ₃ : OModulePresheaf.Hom (OModulePresheaf.ofModules f N₃) (L.eigenSubdatum n hG (χ * ψ)))
    (ψ₃ : OModulePresheaf.Hom (L.eigenSubdatum n hG (χ * ψ)) (OModulePresheaf.ofModules f N₃))
    (h₃ : ∀ (U : A.Opens) (s : (L.eigenSubdatum n hG (χ * ψ)).obj U), φ₃.app U (ψ₃.app U s) = s)
    (h₃' : ∀ (U : A.Opens) (s : (OModulePresheaf.ofModules f N₃).obj U), ψ₃.app U (φ₃.app U s) = s)
    (hfr : ∀ y : A, ∃ V : A.affineOpens, y ∈ V.1 ∧
      ∃ (s : (L.eigenSubdatum n hG χ).obj V.1) (t : (L.eigenSubdatum n hG ψ).obj V.1),
        ∀ (W : A.affineOpens) (hW : W.1 ≤ V.1),
          Function.Bijective (fun a : Γ(A, W.1) => a • (L.eigenSubdatum n hG χ).res hW s) ∧
          Function.Bijective (fun a : Γ(A, W.1) => a • (L.eigenSubdatum n hG ψ).res hW t) ∧
          Function.Bijective (fun a : Γ(A, W.1) => a • (L.eigenSubdatum n hG (χ * ψ)).res hW (L.eigenMul n hG s t))) :
    Nonempty (N₁ ⊗ N₂ ≅ N₃) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nonempty_tensor_iso_of_hom_eigenSubdatum_of_forall_exists_bijective_smul.solution
