import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_finite_etale_isAdicComplete_units_monoidHom_residue_eq

set_option autoImplicit false

universe u w

theorem IsDiscreteValuationRing.exists_finite_etale_isAdicComplete_units_monoidHom_residue_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (p : ℕ) [Fact p.Prime] (hunif : Irreducible (p : R))
    (F : Type w) [Field F] [Fintype F] (r : ℕ) [NeZero r] (hF : Fintype.card F = p ^ r) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : CharZero R')
      (_ : Algebra R R') (_ : Module.Finite R R') (_ : Module.Free R R') (_ : Algebra.Etale R R'),
      IsAdicComplete (IsLocalRing.maximalIdeal R') R' ∧ IsLocalHom (algebraMap R R') ∧
      Irreducible (p : R') ∧ IsUnit ((p ^ r : R') - 1) ∧
      ∃ (χ : Fˣ →* R'ˣ) (ι : F →+* IsLocalRing.ResidueField R'),
        ∀ l : Fˣ, IsLocalRing.residue R' (χ l : R') = ι l := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_finite_etale_isAdicComplete_units_monoidHom_residue_eq.solution
