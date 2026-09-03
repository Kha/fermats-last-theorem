import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isQuadrupleOf
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_deligneDatum_unique
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_drinfeldDatum_isQuadrupleOf
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_isQuadrupleOf_iff_isIsomorphic
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_forall_existsUnique_isQuadrupleOf_and_forall_exists_and_isIsomorphic_iff_of_isNilpotent
attribute [-instance] CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) (hfin : Finite (𝒪 ⧸ Ideal.span {π}))
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) :
    (∀ Q : DrinfeldDatum (K := K) π B, ∃! d : DeligneDatum (K := K) π B, Q.IsQuadrupleOf d) ∧
    (∀ d : DeligneDatum (K := K) π B, ∃ Q : DrinfeldDatum (K := K) π B, Q.IsQuadrupleOf d) ∧
    (∀ (Q Q' : DrinfeldDatum (K := K) π B) (d : DeligneDatum (K := K) π B),
      Q.IsQuadrupleOf d → (Q'.IsQuadrupleOf d ↔ Q'.IsIsomorphic Q)) := by
  refine ⟨fun Q => ?_, fun d => CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf hπ hfin hB d, fun Q Q' d h =>
    CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.isQuadrupleOf_iff_isIsomorphic hπ hB h Q'⟩
  obtain ⟨d, hd⟩ := CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isQuadrupleOf hπ hB Q
  exact ⟨d, hd, fun d' hd' => CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.deligneDatum_unique hπ hd hd'⟩
