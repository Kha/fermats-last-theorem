import Mathlib
import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_apply_sub_mem_maximalIdeal_smul_top_of_triangular

set_option autoImplicit false
theorem GaloisRepAdic.apply_sub_mem_maximalIdeal_smul_top_of_triangular
    {B : Type} [CommRing B] [IsLocalRing B] (ρ : GaloisRepAdic B)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : Module.Basis (Fin 2) B ρ.V) (x y z : B)
    (h0 : ρ.ρ σ (b 0) = x • b 0) (h1 : ρ.ρ σ (b 1) = y • b 0 + z • b 1)
    (hx : x - 1 ∈ IsLocalRing.maximalIdeal B) (hy : y ∈ IsLocalRing.maximalIdeal B)
    (hz : z - 1 ∈ IsLocalRing.maximalIdeal B) (v : ρ.V) :
    ρ.ρ σ v - v ∈ (IsLocalRing.maximalIdeal B) • (⊤ : Submodule B ρ.V) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_apply_sub_mem_maximalIdeal_smul_top_of_triangular.solution
