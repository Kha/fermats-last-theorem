import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_finiteDimensional_of_isCompactOperator_of_forall_apply_eq

set_option autoImplicit false
open Topology

theorem Submodule.finiteDimensional_of_isCompactOperator_of_forall_apply_eq
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {T : E →L[𝕜] E} (hT : IsCompactOperator T) (V : Submodule 𝕜 E) (hV : ∀ v ∈ V, T v = v) :
    FiniteDimensional 𝕜 ↥V := by p2m_exact_reverting @_root_.P2MW.S_Submodule_finiteDimensional_of_isCompactOperator_of_forall_apply_eq.solution
