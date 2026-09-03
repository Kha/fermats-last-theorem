import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_IsAbsolutelyIrreducible_isIrreducible
attribute [-simp] ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq

set_option autoImplicit false

theorem ResidualGaloisRep.IsAbsolutelyIrreducible.isIrreducible {k : Type} [Field k] {ρ : ResidualGaloisRep k}
    (h : ρ.IsAbsolutelyIrreducible) : ρ.IsIrreducible := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_IsAbsolutelyIrreducible_isIrreducible.solution
