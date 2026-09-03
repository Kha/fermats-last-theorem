import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_forall_existsUnique_isQuadrupleOf_and_forall_exists_and_isIsomorphic_iff_of_isNilpotent
attribute [-instance] CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.forall_existsUnique_isQuadrupleOf_and_forall_exists_and_isIsomorphic_iff_of_isNilpotent
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) (hfin : Finite (𝒪 ⧸ Ideal.span {π}))
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) :
    (∀ Q : DrinfeldDatum (K := K) π B, ∃! d : DeligneDatum (K := K) π B, Q.IsQuadrupleOf d) ∧
    (∀ d : DeligneDatum (K := K) π B, ∃ Q : DrinfeldDatum (K := K) π B, Q.IsQuadrupleOf d) ∧
    (∀ (Q Q' : DrinfeldDatum (K := K) π B) (d : DeligneDatum (K := K) π B),
      Q.IsQuadrupleOf d → (Q'.IsQuadrupleOf d ↔ Q'.IsIsomorphic Q)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_forall_existsUnique_isQuadrupleOf_and_forall_exists_and_isIsomorphic_iff_of_isNilpotent.solution
