import Mathlib
import P2M.Util
import P2M.Sol.S_Module_FaithfullyFlat_of_isLocalized_span
set_option Elab.async false
set_option autoImplicit false

theorem Module.FaithfullyFlat.of_isLocalized_span
    {R : Type*} [CommRing R] (s : Set R) (spn : Ideal.span s = ⊤)
    {M : Type*} [AddCommGroup M] [Module R M]
    (Rₛ : s → Type*) [∀ r : s, CommRing (Rₛ r)] [∀ r : s, Algebra R (Rₛ r)]
    [∀ r : s, IsLocalization.Away r.1 (Rₛ r)]
    (Mₛ : s → Type*) [∀ r : s, AddCommGroup (Mₛ r)] [∀ r : s, Module R (Mₛ r)] [∀ r : s, Module (Rₛ r) (Mₛ r)]
    [∀ r : s, IsScalarTower R (Rₛ r) (Mₛ r)]
    (g : ∀ r : s, M →ₗ[R] Mₛ r) [∀ r : s, IsLocalizedModule.Away r.1 (g r)]
    (H : ∀ r : s, Module.FaithfullyFlat (Rₛ r) (Mₛ r)) :
    Module.FaithfullyFlat R M := by p2m_exact_reverting @_root_.P2MW.S_Module_FaithfullyFlat_of_isLocalized_span.solution
