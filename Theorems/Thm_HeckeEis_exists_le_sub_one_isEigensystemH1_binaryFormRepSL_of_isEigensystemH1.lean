import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_le_sub_one_isEigensystemH1_binaryFormRepSL_of_isEigensystemH1

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_le_sub_one_isEigensystemH1_binaryFormRepSL_of_isEigensystemH1
    (p : ℕ) (hp : p.Prime) (N : ℕ) [NeZero N] (S₀ : Set ℕ) (hS₀p : p ∈ S₀)
    (F : Type) [Field F] [CharP F p] (n : ℕ) (lam : ℕ → F)
    (hocc : HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL F n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj F n ℓ) S₀ lam) :
    ∃ a : ℕ, a ≤ p - 1 ∧ ∃ j : ℕ, HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL F a).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj F a ℓ) S₀ (fun ℓ => (ℓ : F) ^ j * lam ℓ) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_le_sub_one_isEigensystemH1_binaryFormRepSL_of_isEigensystemH1.solution
