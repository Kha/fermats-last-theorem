import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import P2M.Util
import P2M.Sol.S_HeckeEis_mem_coeffCoboundaries_of_smul_mem_coeffCoboundaries_of_lt

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.mem_coeffCoboundaries_of_smul_mem_coeffCoboundaries_of_lt
    {R K : Type} [CommRing R] [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (φ : R →+* K) (hφ : Function.Surjective φ) (π : R) (hker : ∀ r : R, φ r = 0 ↔ π ∣ r)
    (hπ : IsSMulRegular R π) (n N : ℕ) (hnp : n < p) (hpN : ¬ p ∣ N)
    (z : ↥(HeckeEis.coeffCocycles
      ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)))
    (hz : π • (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R n)) ∈
      HeckeEis.coeffCoboundaries
        ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)) :
    (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R n)) ∈
      HeckeEis.coeffCoboundaries
        ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_mem_coeffCoboundaries_of_smul_mem_coeffCoboundaries_of_lt.solution
