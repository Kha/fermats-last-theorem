import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallyUnramified_exists_isGalois_forall_algHom_apply_mem

set_option autoImplicit false

universe u

theorem Algebra.FormallyUnramified.exists_isGalois_forall_algHom_apply_mem
    (K : Type u) [Field K] (E : Type u) [CommRing E] [Algebra K E]
    [Module.Finite K E] [Algebra.FormallyUnramified K E]
    (Ω : Type*) [Field Ω] [Algebra K Ω] [Normal K Ω] :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ IsGalois K L ∧
      ∀ (φ : E →ₐ[K] Ω) (e : E), φ e ∈ L := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallyUnramified_exists_isGalois_forall_algHom_apply_mem.solution
