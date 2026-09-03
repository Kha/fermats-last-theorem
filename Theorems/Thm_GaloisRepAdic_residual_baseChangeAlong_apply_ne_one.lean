import Mathlib
import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_residual_baseChangeAlong_apply_ne_one

set_option autoImplicit false
theorem GaloisRepAdic.residual_baseChangeAlong_apply_ne_one
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (h : ρ.residual.ρ σ ≠ 1) :
    (ρ.baseChangeAlong φ hφ).residual.ρ σ ≠ 1 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_residual_baseChangeAlong_apply_ne_one.solution
