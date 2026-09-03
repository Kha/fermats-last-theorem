import Definitions.Def_GaloisRep_Adic
import P2M.Util
namespace P2MW.S_GaloisRepAdic_trace_baseChangeAlong

theorem solution {A : Type} [CommRing A] [IsLocalRing A] {B : Type} [CommRing B] [IsLocalRing B] (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : (ρ.baseChangeAlong φ hφ).trace σ = φ (ρ.trace σ) := by
  letI : Algebra A B := φ.toAlgebra
  exact LinearMap.trace_baseChange (ρ.ρ σ) B
