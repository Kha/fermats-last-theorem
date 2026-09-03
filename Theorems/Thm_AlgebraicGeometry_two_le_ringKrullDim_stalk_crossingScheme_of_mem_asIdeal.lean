import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_two_le_ringKrullDim_stalk_crossingScheme_of_mem_asIdeal

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing MvPolynomial

theorem AlgebraicGeometry.two_le_ringKrullDim_stalk_crossingScheme_of_mem_asIdeal
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
    (E : ℕ) (hE : 1 ≤ E) (w : Oˣ) (a : O) (ha : a = (w : O) * ϖ ^ E)
    (m : ↥(CrossingQuotient.crossingScheme a))
    (hm : CrossingQuotient.U a ∈ m.asIdeal ∧ CrossingQuotient.V a ∈ m.asIdeal) :
    2 ≤ ringKrullDim ((CrossingQuotient.crossingScheme a).presheaf.stalk m) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_two_le_ringKrullDim_stalk_crossingScheme_of_mem_asIdeal.solution
