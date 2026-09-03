import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.TensorProduct.Basic
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u
open CategoryTheory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (M : X.Modules)
    (htriv : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    ∃ e : Γ(Y, i ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U) ≃ₗ[Γ(Y, i ⁻¹ᵁ U)] Γ((Scheme.Modules.pullback i).obj M, i ⁻¹ᵁ U),
      ∀ m : Γ(M, U), e (1 ⊗ₜ m) = (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app U).hom m := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.solution
