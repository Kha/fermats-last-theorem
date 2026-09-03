import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_hom_proj_preimage_basicOpen_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.SmoothProperCurve.FiniteMapData.exists_hom_proj_preimage_basicOpen_eq
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} (𝔉 : SmoothProperCurve.FiniteMapData c ε) :
    ∃ (π : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R))
      (hU : π ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 0) = 𝔉.U)
      (hV : π ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 1) = 𝔉.V),
      π ≫ ProjSpace.π R 1 = c ∧
      (π.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 0)) 𝔉.U hU.ge).hom
          ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 0)).hom (ProjSpace.ratio R 1 0 1)) = 𝔉.f ∧
      (π.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 1)) 𝔉.V hV.ge).hom
          ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 1)).hom (ProjSpace.ratio R 1 1 0)) = 𝔉.g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_hom_proj_preimage_basicOpen_eq.solution
