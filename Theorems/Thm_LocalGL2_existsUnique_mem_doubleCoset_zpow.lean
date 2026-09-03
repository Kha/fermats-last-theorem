import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import P2M.Util
import P2M.Sol.S_LocalGL2_existsUnique_mem_doubleCoset_zpow

open LocalGL2 HeckePair
theorem LocalGL2.existsUnique_mem_doubleCoset_zpow
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) (g : GL (Fin 2) K) :
    ∃! p : ℤ × ℤ, p.1 ≤ p.2 ∧
      g ∈ doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0 ^ p.1 * localRepInf ϖ hϖ0 ^ p.2) := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_existsUnique_mem_doubleCoset_zpow.solution
