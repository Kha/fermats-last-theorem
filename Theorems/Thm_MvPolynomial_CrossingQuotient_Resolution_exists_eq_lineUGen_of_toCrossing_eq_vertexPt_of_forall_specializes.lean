import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionFibrePoints
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_Resolution_exists_eq_lineUGen_of_toCrossing_eq_vertexPt_of_forall_specializes
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.exists_eq_lineUGen_of_toCrossing_eq_vertexPt_of_forall_specializes
    {W : Type u} [CommRing W] (t : W) (e : ℕ) (𝔭 : Ideal W) [𝔭.IsMaximal] (ht : t ∈ 𝔭) (he : 1 ≤ e)
    (o : Resolution t e) (ho : toCrossing t e o = vertexPt t e 𝔭 ht he)
    (hmax : ∀ o' : Resolution t e, o' ⤳ o → t ∈ ((toSpec t e).base o').asIdeal → o' = o) :
    ∃ k : Fin (e - 1), o = lineUGen t e 𝔭 ht ⟨k, by omega⟩ := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_eq_lineUGen_of_toCrossing_eq_vertexPt_of_forall_specializes.solution
