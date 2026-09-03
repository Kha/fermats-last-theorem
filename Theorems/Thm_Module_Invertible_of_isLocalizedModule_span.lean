import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Invertible_of_isLocalizedModule_span

set_option autoImplicit false

open TensorProduct

theorem Module.Invertible.of_isLocalizedModule_span
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (s : Set R) (hs : Ideal.span s = ⊤)
    (Rₚ : ↥s → Type*) [∀ r : ↥s, CommRing (Rₚ r)] [∀ r : ↥s, Algebra R (Rₚ r)]
    [∀ r : ↥s, IsLocalization.Away (r.1 : R) (Rₚ r)]
    (Mₚ : ↥s → Type*) [∀ r : ↥s, AddCommGroup (Mₚ r)] [∀ r : ↥s, Module R (Mₚ r)] [∀ r : ↥s, Module (Rₚ r) (Mₚ r)]
    [∀ r : ↥s, IsScalarTower R (Rₚ r) (Mₚ r)]
    (φ : ∀ r : ↥s, M →ₗ[R] Mₚ r) [∀ r : ↥s, IsLocalizedModule (Submonoid.powers (r.1 : R)) (φ r)]
    (H : ∀ r : ↥s, Module.Invertible (Rₚ r) (Mₚ r)) : Module.Invertible R M := by p2m_exact_reverting @_root_.P2MW.S_Module_Invertible_of_isLocalizedModule_span.solution
