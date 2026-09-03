import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finset_span_eq_top_forall_inEdgeChart_map_away

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_finset_span_eq_top_forall_inEdgeChart_map_away
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪} (hfin : Finite (𝒪 ⧸ Ideal.span {π}))
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (d : DeligneDatum (K := K) π B) :
    ∃ s : Finset B, Ideal.span (s : Set B) = ⊤ ∧ ∀ r ∈ s, ∃ (M' M : FullLattice 𝒪 K),
      M'.1 ≤ M.1 ∧ (∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) ∧
      (∀ 𝔮 : Ideal B, 𝔮.IsPrime → r ∉ 𝔮 → d.EdgeNondegAt π 𝔮 M' M) ∧
      (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away r))).InEdgeChart π M' M := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finset_span_eq_top_forall_inEdgeChart_map_away.solution
