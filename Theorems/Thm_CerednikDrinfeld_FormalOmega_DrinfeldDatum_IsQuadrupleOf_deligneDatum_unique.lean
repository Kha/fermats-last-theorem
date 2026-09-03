import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_deligneDatum_unique

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.deligneDatum_unique
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    {Q : DrinfeldDatum (K := K) π B} {d d' : DeligneDatum (K := K) π B}
    (h : Q.IsQuadrupleOf d) (h' : Q.IsQuadrupleOf d') : d' = d := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_deligneDatum_unique.solution
