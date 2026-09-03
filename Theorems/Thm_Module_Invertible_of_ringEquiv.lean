import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Invertible_of_ringEquiv

set_option autoImplicit false

universe u v

theorem Module.Invertible.of_ringEquiv
    {R R' : Type u} [CommRing R] [CommRing R'] (σ : R ≃+* R')
    (M : Type v) [AddCommGroup M] [Module R' M] [Module.Invertible R' M]
    [Module R M] (hσ : ∀ (r : R) (m : M), r • m = σ r • m) :
    Module.Invertible R M := by p2m_exact_reverting @_root_.P2MW.S_Module_Invertible_of_ringEquiv.solution
