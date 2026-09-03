import Mathlib.GroupTheory.Sylow
import Definitions.Def_SchurMultiplierTrivial
import P2M.Util
import P2M.Sol.S_Ihara_hasTrivialSchurMultiplier_of_sylow

theorem Ihara.hasTrivialSchurMultiplier_of_sylow
    {G : Type*} [Group G] [Finite G]
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G),
      Ihara.HasTrivialSchurMultiplier ↥(P : Subgroup G)) :
    Ihara.HasTrivialSchurMultiplier G := by p2m_exact_reverting @_root_.P2MW.S_Ihara_hasTrivialSchurMultiplier_of_sylow.solution
