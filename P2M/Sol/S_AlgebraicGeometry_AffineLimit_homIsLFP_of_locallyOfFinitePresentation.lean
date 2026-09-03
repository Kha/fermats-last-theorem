import Definitions.Def_AlgebraicGeometry_AffineLimit
import Definitions.Def_AlgebraicGeometry_FGSubalgebra
import Theorems.Thm_AlgebraicGeometry_FGSubalgebra_nonempty_isLimit_specCone
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_AffineLimit_homIsLFP_of_locallyOfFinitePresentation

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    (R : Type u) [CommRing R] {X : Scheme.{u}} (ξ : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation ξ] : AffineLimit.HomIsLFP ξ := by
  refine ⟨fun A _ _ φ hφ ↦ ?_, fun A _ _ A₀ hA₀ φ₀ φ₀' h₀ h₀' hφ ↦ ?_⟩
  · obtain ⟨⟨A₀, hA₀⟩, g, hg, hg'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (FGSubalgebra.specDiagram R A) (FGSubalgebra.specOver R A) ξ (FGSubalgebra.specCone R A)
      (FGSubalgebra.nonempty_isLimit_specCone R A).some φ
      (by rw [FGSubalgebra.specCone_π_comp_specOver]; exact congrArg _ hφ.symm)
    exact ⟨A₀, hA₀, g, hg', hg⟩
  · obtain ⟨⟨A₁, hA₁⟩, ⟨⟨⟨h⟩⟩⟩, H⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
      (FGSubalgebra.specDiagram R A) (FGSubalgebra.specOver R A) ξ (FGSubalgebra.specCone R A)
      (FGSubalgebra.nonempty_isLimit_specCone R A).some (i := Opposite.op ⟨A₀, hA₀⟩) φ₀ φ₀'
      h₀.symm h₀'.symm hφ
    exact ⟨A₁, hA₁, h, H⟩
