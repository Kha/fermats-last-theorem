import Definitions.Def_GaloisRep_ResidualEquiv
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_isEquiv_baseChangeAlong_id

theorem ResidualGaloisRep.isEquiv_baseChangeAlong_id {k : Type} [Field k] (ρ : ResidualGaloisRep k) :
    ρ.IsEquiv (ρ.baseChangeAlong (RingHom.id k)) := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_isEquiv_baseChangeAlong_id.solution
