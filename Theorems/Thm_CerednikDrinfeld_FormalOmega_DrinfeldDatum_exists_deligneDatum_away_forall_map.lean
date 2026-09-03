import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_deligneDatum_away_forall_map

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_deligneDatum_away_forall_map
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) :
    ∃ r : B, r ∉ x.asIdeal ∧ ∃ d : DeligneDatum (K := K) π (Localization.Away r),
      ∀ (y : PrimeSpectrum B), r ∉ y.asIdeal →
        ∀ g : Localization.Away r →ₐ[𝒪] locRing B y,
          (∀ b : B, g (algebraMap B (Localization.Away r) b) = algebraMap B (locRing B y) b) →
          LinearMap.ker (Q.u₀ y) = (d.map π g).line (Q.L₀ y) ∧ LinearMap.ker (Q.u₁ y) = (d.map π g).line (Q.L₁ y) ∧
            (d.map π g).InEdgeChart π (Q.L₀ y) (Q.L₁ y) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_deligneDatum_away_forall_map.solution
