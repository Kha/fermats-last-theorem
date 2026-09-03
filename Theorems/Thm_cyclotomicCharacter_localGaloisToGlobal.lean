import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_cyclotomicCharacter_localGaloisToGlobal

set_option autoImplicit false

theorem cyclotomicCharacter_localGaloisToGlobal (p : ℕ) [Fact p.Prime]
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    cyclotomicCharacter (AlgebraicClosure ℚ) p (localGaloisToGlobal p σ).toRingEquiv =
      cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv := by p2m_exact_reverting @_root_.P2MW.S_cyclotomicCharacter_localGaloisToGlobal.solution
