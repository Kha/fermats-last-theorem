import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_isLocalization_ratLocalizedAt

theorem GaloisRep.isLocalization_ratLocalizedAt
    {p : ℕ} (hp : p.Prime) [(Ideal.span {(p : ℤ)}).IsPrime] :
    IsLocalization.AtPrime (GaloisRep.ratLocalizedAt p) (Ideal.span {(p : ℤ)}) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_isLocalization_ratLocalizedAt.solution
