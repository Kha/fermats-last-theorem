import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_irreducible_natCast_ratLocalizedAt

theorem GaloisRep.irreducible_natCast_ratLocalizedAt (q : ℕ) (hq : q.Prime) :
    Irreducible ((q : ℕ) : GaloisRep.ratLocalizedAt q) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_irreducible_natCast_ratLocalizedAt.solution
