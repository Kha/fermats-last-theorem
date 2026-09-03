import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_ringHom_functionField_germ_eq_and_linearIndependent_of_isPullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicGeometry.exists_ringHom_functionField_germ_eq_and_linearIndependent_of_isPullback
    {κ : Type u} [Field κ] {k : Type u} [Field k] (ι : κ →+* k)
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (c : X ⟶ Spec (CommRingCat.of κ)) (d : Y ⟶ Spec (CommRingCat.of k)) (f : Y ⟶ X)
    (hP : IsPullback f d c (Spec.map (CommRingCat.ofHom ι))) :
    letI := (baseToFunctionField c).toAlgebra
    letI := (baseToFunctionField d).toAlgebra
    ∃ φ : X.functionField →+* Y.functionField,
      (∀ a : κ, φ (baseToFunctionField c a) = baseToFunctionField d (ι a)) ∧
      (∀ (U : X.Opens) [Nonempty (Scheme.Opens.toScheme U)] [Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ U))]
        (s : Γ(X, U)),
        φ (X.germToFunctionField U s) = Y.germToFunctionField (f ⁻¹ᵁ U) ((f.app U).hom s)) ∧
      (∀ {ιx : Type u} (b : ιx → X.functionField),
        LinearIndependent κ b → LinearIndependent k (fun i => φ (b i))) ∧
      (∀ z : Y.functionField, ∃ u ∈ Algebra.adjoin k (Set.range φ), ∃ v ∈ Algebra.adjoin k (Set.range φ),
        v ≠ 0 ∧ z * v = u) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ringHom_functionField_germ_eq_and_linearIndependent_of_isPullback.solution
