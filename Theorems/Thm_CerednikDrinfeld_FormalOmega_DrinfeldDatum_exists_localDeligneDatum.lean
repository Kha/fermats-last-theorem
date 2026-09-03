import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_localDeligneDatum

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_localDeligneDatum
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) :
    ∃ dₓ : DeligneDatum (K := K) π (locRing B x),
      LinearMap.ker (Q.u₀ x) = dₓ.line (Q.L₀ x) ∧ LinearMap.ker (Q.u₁ x) = dₓ.line (Q.L₁ x) ∧
      dₓ.InEdgeChart π (Q.L₀ x) (Q.L₁ x) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_localDeligneDatum.solution
