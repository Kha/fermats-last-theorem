import Mathlib
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_mem_isFrameOn

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {N : ℕ}
    (𝔓 : Scheme.Modules.ProjPresentation M f N) (x : ↥X) :
    ∃ (i : Fin (N + 1)) (U : X.Opens), x ∈ U ∧ Scheme.Modules.IsFrameOn (𝔓.σ i) U := by
  have hcov := AlgebraicGeometry.Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
    (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) R) (ProjSpace.irrelevant_le_span_X R N)
  have hx : 𝔓.toProj.base x ∈ (⨆ i, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) := by
    rw [hcov]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨i, 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i), hi,
    fun W _ hWV => 𝔓.frame i W hWV⟩
