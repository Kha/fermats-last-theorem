import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DeligneDatum_existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart
attribute [-instance] CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀

set_option autoImplicit false

open scoped TensorProduct
p2m_open "LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega~exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent"

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) :

    (∀ d : DeligneDatum (K := K) π B, d.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K) →
        ∃! x : chartERing 𝒪 π q →ₐ[𝒪] B,
          d.line (stdFullLattice K) =
            Submodule.span B {(x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} ∧
          d.line (FullLattice.act g (stdFullLattice K)) =
            (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
              (actBaseChange B g (stdFullLattice K)).toLinearMap) ∧

    (∀ x : chartERing 𝒪 π q →ₐ[𝒪] B,
        ∃! d : DeligneDatum (K := K) π B,
          (d.line (stdFullLattice K) =
            Submodule.span B {(x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} ∧
          d.line (FullLattice.act g (stdFullLattice K)) =
            (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
              (actBaseChange B g (stdFullLattice K)).toLinearMap) ∧
          d.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K)) ∧

    (∀ (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (d : DeligneDatum (K := K) π B) (x : chartERing 𝒪 π q →ₐ[𝒪] B),
        (d.line (stdFullLattice K) =
            Submodule.span B {(x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} ∧
          d.line (FullLattice.act g (stdFullLattice K)) =
            (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
              (actBaseChange B g (stdFullLattice K)).toLinearMap) →
          ((Omega K π).map φ d).line (stdFullLattice K) =
            Submodule.span B' {((φ.comp x) (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B') ⊗ₜ[𝒪] stdBasisVec K 1} ∧
          ((Omega K π).map φ d).line (FullLattice.act g (stdFullLattice K)) =
            (Submodule.span B' {(1 : B') ⊗ₜ[𝒪] stdBasisVec K 0 + ((φ.comp x) (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
              (actBaseChange B' g (stdFullLattice K)).toLinearMap) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart.solution
