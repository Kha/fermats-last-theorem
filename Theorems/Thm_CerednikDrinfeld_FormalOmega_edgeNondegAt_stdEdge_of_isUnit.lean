import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_edgeNondegAt_stdEdge_of_isUnit

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.edgeNondegAt_stdEdge_of_isUnit
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (B : Type) [CommRing B] [Algebra 𝒪 B] (ξ η : B) (hξη : ξ * η = algebraMap 𝒪 B π)
    (hξ : IsUnit (ξ ^ (q - 1) - 1)) (hη : IsUnit (η ^ (q - 1) - 1))
    (𝔭 : Ideal B) (h𝔭 : 𝔭.IsPrime) (hπ𝔭 : algebraMap 𝒪 B π ∈ 𝔭) :
    (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1 ≤ (stdFullLattice (𝒪 := 𝒪) K).1 ∧
    (∀ v : ↥(stdFullLattice (𝒪 := 𝒪) K).1,
      (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1) ∧
    (∀ v : ↥(stdFullLattice (𝒪 := 𝒪) K).1, (v : Fin 2 → K) ∉ (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1 →
      (1 : B) ⊗ₜ[𝒪] v ∉
        Submodule.span B {ξ ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1} ⊔
          (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)))) ∧
    (∀ v' : ↥(FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K)).1,
      (¬ ∃ w : ↥(stdFullLattice (𝒪 := 𝒪) K).1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)) →
      (1 : B) ⊗ₜ[𝒪] v' ∉
        (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + η ⊗ₜ[𝒪] stdBasisVec K 1}).map
            (actBaseChange B g (stdFullLattice (𝒪 := 𝒪) K)).toLinearMap ⊔
          (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (FullLattice.act g (stdFullLattice (𝒪 := 𝒪) K))))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_edgeNondegAt_stdEdge_of_isUnit.solution
