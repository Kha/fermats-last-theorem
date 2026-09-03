import Mathlib.RingTheory.Derivation.Basic
import P2M.Util
import P2M.Sol.S_Derivation_add_mulLeft_pow_char
set_option autoImplicit false
universe u v

theorem Derivation.add_mulLeft_pow_char {R : Type u} {F : Type v} [CommRing R] [CommRing F]
    [Algebra R F] (p : ℕ) [Fact p.Prime] [CharP F p] (d : Derivation R F F) (a : F) :
    (d.toLinearMap + LinearMap.mulLeft R a) ^ p
      = d.toLinearMap ^ p + LinearMap.mulLeft R (a ^ p + (d.toLinearMap ^ (p - 1)) a) := by p2m_exact_reverting @_root_.P2MW.S_Derivation_add_mulLeft_pow_char.solution
