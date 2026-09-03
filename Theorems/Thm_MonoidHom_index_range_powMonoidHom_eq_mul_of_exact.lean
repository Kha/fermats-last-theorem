import Mathlib
import P2M.Util
import P2M.Sol.S_MonoidHom_index_range_powMonoidHom_eq_mul_of_exact

set_option autoImplicit false
theorem MonoidHom.index_range_powMonoidHom_eq_mul_of_exact {G U F : Type*} [CommGroup G] [CommGroup U]
    [CommGroup F] (ι : U →* G) (φ : G →* F) (hι : Function.Injective ι) (hφ : Function.Surjective φ)
    (hexact : ι.range = φ.ker) {n : ℕ} (hF : ∀ x : F, x ^ n = 1 → x = 1) :
    (powMonoidHom n : G →* G).range.index
      = (powMonoidHom n : F →* F).range.index * (powMonoidHom n : U →* U).range.index := by p2m_exact_reverting @_root_.P2MW.S_MonoidHom_index_range_powMonoidHom_eq_mul_of_exact.solution
