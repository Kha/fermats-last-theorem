import Mathlib
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_embedding_place_range_eq_compl_placesOf_of_isSectional

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicCurve

theorem exists_embedding_place_range_eq_compl_placesOf_of_isSectional
    {k : Type u} [Field k] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsProper c] [SmoothOfRelativeDimension 1 c]
    {ι : Type w} (σ : ι → (Spec (CommRingCat.of k) ⟶ X)) (hσ : 𝒱.IsSectional c σ) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∃ p : ι ↪ AlgebraicCurve.Place k X.functionField,
      Set.range p = (AlgebraicCurve.placesOf c 𝒱.U1)ᶜ ∧
      ∀ i, (algebraMap (X.presheaf.stalk ((σ i).base (IsLocalRing.closedPoint k))) X.functionField).range =
        (p i).toValuationSubring.toSubring := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_embedding_place_range_eq_compl_placesOf_of_isSectional.solution

end AlgebraicCurve
