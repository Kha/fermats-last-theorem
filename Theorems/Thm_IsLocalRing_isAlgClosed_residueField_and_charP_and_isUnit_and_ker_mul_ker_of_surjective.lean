import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isAlgClosed_residueField_and_charP_and_isUnit_and_ker_mul_ker_of_surjective

set_option autoImplicit false

open IsLocalRing

universe u

theorem IsLocalRing.isAlgClosed_residueField_and_charP_and_isUnit_and_ker_mul_ker_of_surjective
    {B B' : Type u} [CommRing B] [IsLocalRing B] [CommRing B'] [IsLocalRing B']
    (σ : B' →+* B) (hσ : Function.Surjective σ) (hsmall : RingHom.ker σ * maximalIdeal B' = ⊥)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p] [IsAlgClosed (ResidueField B)]
    (q q' : ℕ) [Fact q.Prime] [Fact q'.Prime] (hpq : p ≠ q) (hpq' : p ≠ q') :
    IsAlgClosed (ResidueField B') ∧ CharP (ResidueField B') p ∧
      IsUnit ((q * q' : ℕ) : B') ∧ RingHom.ker σ * RingHom.ker σ = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isAlgClosed_residueField_and_charP_and_isUnit_and_ker_mul_ker_of_surjective.solution
