import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isFinite_pullback_and_finrank_sections_eq_mul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isFinite_pullback_and_finrank_sections_eq_mul
    {κ : Type u} [Field κ] {Y Z : Scheme.{u}}
    (qY : Y ⟶ Spec (.of κ)) (qZ : Z ⟶ Spec (.of κ)) [IsFinite qY] [IsFinite qZ] :
    IsFinite (pullback.fst qY qZ ≫ qY) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst qY qZ ≫ qY) ⊤
     letI := Scheme.TwoAffineOpenCover.algebraOfHom qY ⊤
     letI := Scheme.TwoAffineOpenCover.algebraOfHom qZ ⊤
     Module.finrank κ Γ(pullback qY qZ, ⊤) = Module.finrank κ Γ(Y, ⊤) * Module.finrank κ Γ(Z, ⊤)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isFinite_pullback_and_finrank_sections_eq_mul.solution
