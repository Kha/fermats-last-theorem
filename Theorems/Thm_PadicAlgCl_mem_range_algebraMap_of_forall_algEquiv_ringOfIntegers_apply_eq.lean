import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers
import P2M.Util
import P2M.Sol.S_PadicAlgCl_mem_range_algebraMap_of_forall_algEquiv_ringOfIntegers_apply_eq

set_option autoImplicit false

theorem PadicAlgCl.mem_range_algebraMap_of_forall_algEquiv_ringOfIntegers_apply_eq
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (K' : Type) [Field K'] [Algebra (PadicAlgCl.ringOfIntegers p K) K']
    [IsFractionRing (PadicAlgCl.ringOfIntegers p K) K']
    [Algebra K' (PadicAlgCl p)] [IsScalarTower (PadicAlgCl.ringOfIntegers p K) K' (PadicAlgCl p)]
    (x : PadicAlgCl p)
    (hx : ∀ τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p, τ x = x) :
    x ∈ Set.range (algebraMap K' (PadicAlgCl p)) := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_mem_range_algebraMap_of_forall_algEquiv_ringOfIntegers_apply_eq.solution
