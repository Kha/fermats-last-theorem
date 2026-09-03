import Definitions.Def_GaloisRep_StrictOrdinary
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_isStrictOrdinaryAt_ofResidualGaloisRep_of_baseChangeAlong

theorem ResidualGaloisRep.isStrictOrdinaryAt_ofResidualGaloisRep_of_baseChangeAlong
    {k k' : Type} [Field k] [Field k'] (ψ : k →+* k') (ρ : ResidualGaloisRep k)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : (GaloisRepAdic.ofResidualGaloisRep (ρ.baseChangeAlong ψ)).IsStrictOrdinaryAt p) :
    (GaloisRepAdic.ofResidualGaloisRep ρ).IsStrictOrdinaryAt p := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_isStrictOrdinaryAt_ofResidualGaloisRep_of_baseChangeAlong.solution
