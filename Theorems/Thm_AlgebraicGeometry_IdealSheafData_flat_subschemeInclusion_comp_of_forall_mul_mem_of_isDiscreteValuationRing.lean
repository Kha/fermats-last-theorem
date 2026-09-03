import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IdealSheafData_flat_subschemeInclusion_comp_of_forall_mul_mem_of_isDiscreteValuationRing

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.IdealSheafData.flat_subschemeInclusion_comp_of_forall_mul_mem_of_isDiscreteValuationRing
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of O)) (J : X.IdealSheafData)
    (hsat : ∀ (ϖ : O), Irreducible ϖ → ∀ (U : X.affineOpens) (s : Γ(X, U)),
        X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op
            (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)) * s ∈ J.ideal U →
          s ∈ J.ideal U) :
    Flat (J.subschemeι ≫ q) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IdealSheafData_flat_subschemeInclusion_comp_of_forall_mul_mem_of_isDiscreteValuationRing.solution
