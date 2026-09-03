import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_Algebra_FormallyUnramified_algEquiv_apply_eq_of_mem_inertiaSubgroupIn_padicIntegers

set_option autoImplicit false

universe v

open scoped PadicInt

theorem Algebra.FormallyUnramified.algEquiv_apply_eq_of_mem_inertiaSubgroupIn_padicIntegers
    (p : ℕ) [Fact p.Prime]
    (B : Type v) [CommRing B] [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B]
    [Algebra.FormallyUnramified ℤ_[p] B]
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hσ : σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p])
    (h : B →ₐ[ℤ_[p]] PadicAlgCl p) (y : B) : σ (h y) = h y := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallyUnramified_algEquiv_apply_eq_of_mem_inertiaSubgroupIn_padicIntegers.solution
