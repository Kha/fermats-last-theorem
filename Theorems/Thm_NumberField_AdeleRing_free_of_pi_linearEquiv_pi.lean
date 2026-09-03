import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_AdeleRing_free_of_pi_linearEquiv_pi

set_option autoImplicit false

open NumberField

theorem NumberField.AdeleRing.free_of_pi_linearEquiv_pi
    (F : Type) [Field F] [NumberField F] (m n : ℕ) (hn : 0 < n)
    (P : Type) [AddCommGroup P] [Module (AdeleRing (𝓞 F) F) P]
    (f : (Fin n → P) ≃ₗ[AdeleRing (𝓞 F) F] (Fin (m * n) → AdeleRing (𝓞 F) F)) :
    Module.Free (AdeleRing (𝓞 F) F) P := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_free_of_pi_linearEquiv_pi.solution
