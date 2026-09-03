import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_fg_forall_lineBaseChange_eq

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_fg_forall_lineBaseChange_eq
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) (L : FullLattice 𝒪 K) :
    ∃ r : B, r ∉ x.asIdeal ∧ ∃ N : Submodule B (latticeBaseChange 𝒪 K B L), N.FG ∧
      ∀ (y : PrimeSpectrum B), r ∉ y.asIdeal → ∀ dy : DeligneDatum (K := K) π (locRing B y),
        LinearMap.ker (Q.u₀ y) = dy.line (Q.L₀ y) → LinearMap.ker (Q.u₁ y) = dy.line (Q.L₁ y) →
        dy.InEdgeChart π (Q.L₀ y) (Q.L₁ y) →
          lineBaseChange (toLocRing B y) L N = dy.line L := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_fg_forall_lineBaseChange_eq.solution
