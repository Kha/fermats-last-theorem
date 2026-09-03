import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_FLTPrelim_ModularRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_residual_eigensystem_of_isResiduallyModularOfLevel

theorem WeierstrassCurve.exists_residual_eigensystem_of_isResiduallyModularOfLevel (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ) {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] (hp𝒪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) (S : Finset ℕ) (_hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S) (hbadS : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → q ∈ S) {N : ℕ} [NeZero N] (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) (hres : W.IsResiduallyModularOfLevel p N) (hint : CuspForm.HasIntegralStructure N 2) : ∃ θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪, ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)), θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) = IsLocalRing.residue 𝒪 ((W.apOfModel ℓ : ℤ) : 𝒪) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_residual_eigensystem_of_isResiduallyModularOfLevel.solution
