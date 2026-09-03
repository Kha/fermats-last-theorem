import Mathlib
import P2M.Util
import P2M.Sol.S_CharacterModule_natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet

theorem CharacterModule.natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet
    (A : Type*) [CommRing A] (G : Type*) [AddCommGroup G] [Module A G]
    (s : Set A) (hs : s.Finite) (hfin : Finite ↥(Submodule.torsionBySet A G s)) :
    Nat.card (CharacterModule G ⧸ (Ideal.span s • (⊤ : Submodule A (CharacterModule G))))
      = Nat.card ↥(Submodule.torsionBySet A G s) := by p2m_exact_reverting @_root_.P2MW.S_CharacterModule_natCard_quotient_ideal_smul_top_eq_natCard_torsionBySet.solution
