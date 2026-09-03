import Mathlib
import Definitions.Def_ProjectiveLineMatrixAction
import Definitions.Def_HeckeEis_BinaryFormRep
import P2M.Util
import P2M.Sol.S_HeckeEis_binaryFormEval_binaryFormAlphaAdj

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.binaryFormEval_binaryFormAlphaAdj (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p] (ℓ : ℕ) (hℓ : p.Coprime ℓ) :
    HeckeEis.binaryFormEval p K ∘ₗ HeckeEis.binaryFormAlphaAdj K (p - 1) ℓ
      = HeckeEis.projLineAlphaAdj p K ℓ ∘ₗ HeckeEis.binaryFormEval p K := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_binaryFormEval_binaryFormAlphaAdj.solution
