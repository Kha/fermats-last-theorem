import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_IsAbsolutelyIrreducible_of_isEquiv

set_option autoImplicit false
theorem ResidualGaloisRep.IsAbsolutelyIrreducible.of_isEquiv
    {k : Type} [Field k] {ρ₁ ρ₂ : ResidualGaloisRep k} (e : ρ₁.IsEquiv ρ₂) (h : ρ₁.IsAbsolutelyIrreducible) :
    ρ₂.IsAbsolutelyIrreducible := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_IsAbsolutelyIrreducible_of_isEquiv.solution
