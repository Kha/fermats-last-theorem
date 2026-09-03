import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_localGaloisToGlobal_apply_eq_of_mem_decompositionSubgroup_padicPlace

set_option autoImplicit false
theorem GaloisRepAdic.exists_localGaloisToGlobal_apply_eq_of_mem_decompositionSubgroup_padicPlace
    {B : Type} [CommRing B] [IsLocalRing B] [Finite B] (p : ℕ) [Fact p.Prime] (ρ : GaloisRepAdic B)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ (padicPlace p).decompositionSubgroup ℚ) :
    ∃ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), ρ.ρ (localGaloisToGlobal p g) = ρ.ρ σ := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_localGaloisToGlobal_apply_eq_of_mem_decompositionSubgroup_padicPlace.solution
