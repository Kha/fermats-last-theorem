import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_mem_smoothLocus_of_isRegularLocalRing_stalk_of_ringKrullDim_le_one_of_perfectField

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.mem_smoothLocus_of_isRegularLocalRing_stalk_of_ringKrullDim_le_one_of_perfectField
    {K : Type u} [Field K] [PerfectField K] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFinitePresentation g]
    (y : ↥Y) (hreg : IsRegularLocalRing (Y.presheaf.stalk y))
    (hdim : ringKrullDim (Y.presheaf.stalk y) ≤ 1) :
    y ∈ g.smoothLocus := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_mem_smoothLocus_of_isRegularLocalRing_stalk_of_ringKrullDim_le_one_of_perfectField.solution
