import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_inEdgeChart_and_line_eq

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_inEdgeChart_and_line_eq
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    {M' M : FullLattice 𝒪 K} (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) (N' : Submodule B (latticeBaseChange 𝒪 K B M'))
    [Module.Invertible B (latticeBaseChange 𝒪 K B M ⧸ N)] [Module.Invertible B (latticeBaseChange 𝒪 K B M' ⧸ N')]
    (hmono : N'.map (inclBaseChange B hle) ≤ N)
    (hsmul : N.map ((smulInto π hπM).baseChange B :
      latticeBaseChange 𝒪 K B M →ₗ[B] latticeBaseChange 𝒪 K B M') ≤ N')
    (h₁ : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → ∀ v : ↥M.1, (v : Fin 2 → K) ∉ M'.1 →
      (1 : B) ⊗ₜ[𝒪] v ∉ N ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)))
    (h₂ : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → ∀ v' : ↥M'.1,
      (¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = algebraMap 𝒪 K π • (w : Fin 2 → K)) →
      (1 : B) ⊗ₜ[𝒪] v' ∉ N' ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M'))) :
    ∃ d : DeligneDatum (K := K) π B, d.line M = N ∧ d.line M' = N' ∧ d.InEdgeChart π M' M := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_inEdgeChart_and_line_eq.solution
