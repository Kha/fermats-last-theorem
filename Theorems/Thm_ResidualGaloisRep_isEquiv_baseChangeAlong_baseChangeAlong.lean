import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_isEquiv_baseChangeAlong_baseChangeAlong

set_option autoImplicit false
theorem ResidualGaloisRep.isEquiv_baseChangeAlong_baseChangeAlong
    {k k' k'' : Type} [Field k] [Field k'] [Field k''] (ψ : k →+* k') (ψ' : k' →+* k'') (ρ : ResidualGaloisRep k) :
    ((ρ.baseChangeAlong ψ).baseChangeAlong ψ').IsEquiv (ρ.baseChangeAlong (ψ'.comp ψ)) := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_isEquiv_baseChangeAlong_baseChangeAlong.solution
