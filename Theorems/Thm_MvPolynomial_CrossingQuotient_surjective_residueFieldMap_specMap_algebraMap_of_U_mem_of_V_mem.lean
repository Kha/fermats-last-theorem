import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_surjective_residueFieldMap_specMap_algebraMap_of_U_mem_of_V_mem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

theorem MvPolynomial.CrossingQuotient.surjective_residueFieldMap_specMap_algebraMap_of_U_mem_of_V_mem
    {O : Type} [CommRing O] (a : O) (q : ↥(CrossingQuotient.crossingScheme a))
    (hU : CrossingQuotient.U a ∈ q.asIdeal) (hV : CrossingQuotient.V a ∈ q.asIdeal) :
    Function.Surjective
      ((Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O a)))).residueFieldMap q).hom := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_surjective_residueFieldMap_specMap_algebraMap_of_U_mem_of_V_mem.solution
