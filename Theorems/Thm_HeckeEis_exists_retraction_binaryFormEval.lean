import Mathlib
import Definitions.Def_ProjectiveLineMatrixAction
import Definitions.Def_HeckeEis_BinaryFormRep
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_retraction_binaryFormEval

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_retraction_binaryFormEval (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] :
    ∃ r : (ModularCurve.ProjectiveLine (ZMod p) → K) →ₗ[K] HeckeEis.BinaryForm K (p - 1),
      r ∘ₗ HeckeEis.binaryFormEval p K = LinearMap.id ∧
      (∀ g : SL(2, ℤ), r ∘ₗ HeckeEis.projLineRepSL p K g = HeckeEis.binaryFormRepSL K (p - 1) g ∘ₗ r) ∧
      (∀ ℓ : ℕ, p.Coprime ℓ →
        r ∘ₗ HeckeEis.projLineAlphaAdj p K ℓ = HeckeEis.binaryFormAlphaAdj K (p - 1) ℓ ∘ₗ r) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_retraction_binaryFormEval.solution
