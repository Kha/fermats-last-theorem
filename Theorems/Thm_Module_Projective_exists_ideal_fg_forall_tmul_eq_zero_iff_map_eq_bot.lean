import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Projective_exists_ideal_fg_forall_tmul_eq_zero_iff_map_eq_bot

set_option autoImplicit false
universe u v
open TensorProduct

theorem Module.Projective.exists_ideal_fg_forall_tmul_eq_zero_iff_map_eq_bot
    (B : Type u) [CommRing B] (M : Type v) [AddCommGroup M] [Module B M]
    [Module.Finite B M] [Module.Projective B M] (x : M) :
    ∃ J : Ideal B, J.FG ∧ ∀ (A : Type u) [CommRing A] (φ : B →+* A),
      (letI : Algebra B A := φ.toAlgebra; ((1 : A) ⊗ₜ[B] x : A ⊗[B] M) = 0) ↔ Ideal.map φ J = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_Module_Projective_exists_ideal_fg_forall_tmul_eq_zero_iff_map_eq_bot.solution
