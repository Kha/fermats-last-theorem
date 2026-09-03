import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_exists_isDiscreteValuationRing_ringHom_comp_eq_of_ringKrullDim_le_two_of_isAdicComplete_of_natCast_ne_zero
attribute [-instance] instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open IsLocalRing

theorem IsRegularLocalRing.exists_isDiscreteValuationRing_ringHom_comp_eq_of_ringKrullDim_le_two_of_isAdicComplete_of_natCast_ne_zero
    (Ry : Type) [CommRing Ry] [IsRegularLocalRing Ry] (hd : ringKrullDim Ry ≤ 2) [IsAdicComplete (maximalIdeal Ry) Ry]
    (p : ℕ) [Fact p.Prime] (hp : ((p : ℕ) : Ry) ≠ 0)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (ι₀ : (Ry ⧸ maximalIdeal Ry ^ (0 + 1)) →+* k) (hι₀ : Function.Bijective ι₀) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (_ : CharZero R)
      (ψ : Ry →+* R) (φ : R →+* k),
      Function.Surjective φ ∧ IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
      φ.comp ψ = ι₀.comp (Ideal.Quotient.mk (maximalIdeal Ry ^ (0 + 1))) := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_exists_isDiscreteValuationRing_ringHom_comp_eq_of_ringKrullDim_le_two_of_isAdicComplete_of_natCast_ne_zero.solution
