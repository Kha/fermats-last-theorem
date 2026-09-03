import Mathlib
import Definitions.Def_ProjectiveLineMatrixAction
import Definitions.Def_HeckeEis_BinaryFormRep
import P2M.Util
import P2M.Sol.S_HeckeEis_binaryFormEval_binaryFormRepSL

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.binaryFormEval_binaryFormRepSL (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p] (g : SL(2, ℤ)) :
    HeckeEis.binaryFormEval p K ∘ₗ HeckeEis.binaryFormRepSL K (p - 1) g
      = HeckeEis.projLineRepSL p K g ∘ₗ HeckeEis.binaryFormEval p K := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_binaryFormEval_binaryFormRepSL.solution
