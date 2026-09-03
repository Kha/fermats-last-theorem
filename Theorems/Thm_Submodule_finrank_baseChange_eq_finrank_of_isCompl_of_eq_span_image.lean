import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_finrank_baseChange_eq_finrank_of_isCompl_of_eq_span_image

set_option autoImplicit false

open scoped TensorProduct

theorem Submodule.finrank_baseChange_eq_finrank_of_isCompl_of_eq_span_image
    {S : Type} [CommRing S] {K : Type} [Field K] [Algebra S K]
    (L₀ L₁ : Submodule S (Fin 2 → S)) (hL : IsCompl L₀ L₁)
    (M₀ M₁ : Submodule K (Fin 2 → K)) (hM : IsCompl M₀ M₁)
    (h₀ : M₀ = Submodule.span K ((fun v : Fin 2 → S => ⇑(algebraMap S K) ∘ v) '' (L₀ : Set (Fin 2 → S))))
    (h₁ : M₁ = Submodule.span K ((fun v : Fin 2 → S => ⇑(algebraMap S K) ∘ v) '' (L₁ : Set (Fin 2 → S)))) :
    Module.finrank K (K ⊗[S] ↥L₀) = Module.finrank K ↥M₀ ∧ Module.finrank K (K ⊗[S] ↥L₁) = Module.finrank K ↥M₁ := by p2m_exact_reverting @_root_.P2MW.S_Submodule_finrank_baseChange_eq_finrank_of_isCompl_of_eq_span_image.solution
