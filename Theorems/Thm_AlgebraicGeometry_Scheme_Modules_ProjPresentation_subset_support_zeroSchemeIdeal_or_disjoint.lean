import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_subset_support_zeroSchemeIdeal_or_disjoint

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.subset_support_zeroSchemeIdeal_or_disjoint
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [IsProper t]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) {N : ℕ} (𝔓 : M.ProjPresentation t N)
    (Z : Set X) (hZ : IsClosed Z) (hZ' : IsIrreducible Z)
    (y : Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)) (hy : IsClosed ({y} : Set _))
    (hZy : Z ⊆ 𝔓.toProj.base ⁻¹' {y}) (s : 𝟙_ X.Modules ⟶ M) :
    Z ⊆ (Scheme.Modules.zeroSchemeIdeal s).support ∨ Disjoint Z (Scheme.Modules.zeroSchemeIdeal s).support := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_subset_support_zeroSchemeIdeal_or_disjoint.solution
