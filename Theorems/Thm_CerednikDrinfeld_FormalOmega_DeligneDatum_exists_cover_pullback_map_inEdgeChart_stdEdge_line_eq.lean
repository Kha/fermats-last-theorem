import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_cover_pullback_map_inEdgeChart_stdEdge_line_eq

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_cover_pullback_map_inEdgeChart_stdEdge_line_eq
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (d : DeligneDatum (K := K) π B) :
    ∃ s : Finset B, Ideal.span (s : Set B) = ⊤ ∧ ∀ r ∈ s,
      ∃ (h : Matrix.GeneralLinearGroup (Fin 2) K) (x : chartERing 𝒪 π q →ₐ[𝒪] Localization.Away r),
        (DeligneDatum.pullback π (Localization.Away r) h
            (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away r)))).InEdgeChart π
          (FullLattice.act g (stdFullLattice K)) (stdFullLattice K) ∧
        (DeligneDatum.pullback π (Localization.Away r) h
            (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away r)))).line (stdFullLattice K) =
          Submodule.span (Localization.Away r)
            {(x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : Localization.Away r) ⊗ₜ[𝒪] stdBasisVec K 1} ∧
        (DeligneDatum.pullback π (Localization.Away r) h
            (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away r)))).line (FullLattice.act g (stdFullLattice K)) =
          (Submodule.span (Localization.Away r)
            {(1 : Localization.Away r) ⊗ₜ[𝒪] stdBasisVec K 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
            (actBaseChange (Localization.Away r) g (stdFullLattice K)).toLinearMap := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_cover_pullback_map_inEdgeChart_stdEdge_line_eq.solution
