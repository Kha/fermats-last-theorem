import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_trace_baseChangeAlong

theorem GaloisRepAdic.trace_baseChangeAlong {A : Type} [CommRing A] [IsLocalRing A] {B : Type} [CommRing B] [IsLocalRing B] (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : (ρ.baseChangeAlong φ hφ).trace σ = φ (ρ.trace σ) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_trace_baseChangeAlong.solution
