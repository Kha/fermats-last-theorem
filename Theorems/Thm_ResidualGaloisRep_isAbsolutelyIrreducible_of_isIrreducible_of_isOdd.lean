import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_isAbsolutelyIrreducible_of_isIrreducible_of_isOdd

theorem ResidualGaloisRep.isAbsolutelyIrreducible_of_isIrreducible_of_isOdd {k : Type} [Field k]
    (ρ : ResidualGaloisRep k) (h2 : (2 : k) ≠ 0) (hirr : ρ.IsIrreducible) (hodd : ρ.IsOdd) :
    ρ.IsAbsolutelyIrreducible := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_isAbsolutelyIrreducible_of_isIrreducible_of_isOdd.solution
