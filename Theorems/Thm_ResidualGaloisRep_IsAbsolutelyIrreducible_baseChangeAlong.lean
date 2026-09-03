import Definitions.Def_GaloisRep_ResidualEquiv
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_IsAbsolutelyIrreducible_baseChangeAlong

open Module LinearMap
theorem ResidualGaloisRep.IsAbsolutelyIrreducible.baseChangeAlong
    {k k' : Type} [Field k] [Field k'] {ρ : ResidualGaloisRep k}
    (hρ : ρ.IsAbsolutelyIrreducible) (φ : k →+* k') :
    (ρ.baseChangeAlong φ).IsAbsolutelyIrreducible := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_IsAbsolutelyIrreducible_baseChangeAlong.solution
