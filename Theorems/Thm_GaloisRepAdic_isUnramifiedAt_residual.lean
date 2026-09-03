import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isUnramifiedAt_residual

theorem GaloisRepAdic.isUnramifiedAt_residual {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) {q : ℕ} (h : ρ.IsUnramifiedAt q) : ρ.residual.IsUnramifiedAt q := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isUnramifiedAt_residual.solution
