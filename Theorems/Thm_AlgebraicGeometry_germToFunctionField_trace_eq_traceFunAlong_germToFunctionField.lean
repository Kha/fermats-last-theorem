import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_germToFunctionField_trace_eq_traceFunAlong_germToFunctionField

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicGeometry.germToFunctionField_trace_eq_traceFunAlong_germToFunctionField
    {K : Type u} [Field K] {X Y : Scheme.{u}} (cX : X ⟶ Spec (.of K)) (cY : Y ⟶ Spec (.of K))
    [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) [IsAffineHom π] (hπ : π ≫ cX = cY)
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] [Nonempty (π ⁻¹ᵁ U : Y.Opens)] :
    letI := (AlgebraicCurve.baseToFunctionField cX).toAlgebra
    letI := (AlgebraicCurve.baseToFunctionField cY).toAlgebra
    letI : Algebra Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
    ∀ [Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U)] [Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U)]
      (φ : X.functionField →ₐ[K] Y.functionField)
      (hφπ : Y.fromSpecStalk (genericPoint Y) ≫ π =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.fromSpecStalk (genericPoint X))
      (g : Γ(Y, π ⁻¹ᵁ U)),
      (X.germToFunctionField U).hom (Algebra.trace Γ(X, U) Γ(Y, π ⁻¹ᵁ U) g) =
        AlgebraicCurve.traceFunAlong φ ((Y.germToFunctionField (π ⁻¹ᵁ U)).hom g) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_germToFunctionField_trace_eq_traceFunAlong_germToFunctionField.solution
