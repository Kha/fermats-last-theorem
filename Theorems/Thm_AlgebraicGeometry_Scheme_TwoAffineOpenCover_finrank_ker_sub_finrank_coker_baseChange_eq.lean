import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_ker_sub_finrank_coker_baseChange_eq
attribute [-simp] TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_ker_sub_finrank_coker_baseChange_eq
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (CommRingCat.of R))
    [Flat c]
    [Module.Finite R (𝒱.structureSheafSections c).H0] [Module.Finite R (𝒱.structureSheafSections c).H1]
    (K : Type u) [Field K] [Algebra R K] (K' : Type u) [Field K'] [Algebra R K'] :
    (Module.finrank K (LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange K)) : ℤ) -
        Module.finrank K ((K ⊗[R] (𝒱.cover c).A01) ⧸
          LinearMap.range ((𝒱.structureSheafSections c).cechDiff.baseChange K)) =
      (Module.finrank K' (LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange K')) : ℤ) -
        Module.finrank K' ((K' ⊗[R] (𝒱.cover c).A01) ⧸
          LinearMap.range ((𝒱.structureSheafSections c).cechDiff.baseChange K')) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_ker_sub_finrank_coker_baseChange_eq.solution
