import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_etale_dvr_residueField_equiv_card_algEquiv_eq_of_isAdicComplete

set_option autoImplicit false

universe u

theorem IsDiscreteValuationRing.exists_etale_dvr_residueField_equiv_card_algEquiv_eq_of_isAdicComplete
    (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (k : Type u) [Field k] [Algebra (IsLocalRing.ResidueField W) k]
    [FiniteDimensional (IsLocalRing.ResidueField W) k]
    [Algebra.IsSeparable (IsLocalRing.ResidueField W) k] :
    ∃ (W' : Type u) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W') W') (_ : Algebra W W')
      (_ : Module.Finite W W') (_ : Module.Free W W') (_ : Module.Flat W W') (_ : FaithfulSMul W W')
      (_ : Algebra.Etale W W')
      (ι : IsLocalRing.ResidueField W' ≃+* k),
      Ideal.map (algebraMap W W') (IsLocalRing.maximalIdeal W) = IsLocalRing.maximalIdeal W' ∧
      (∀ w : W, ι (IsLocalRing.residue W' (algebraMap W W' w)) =
        algebraMap (IsLocalRing.ResidueField W) k (IsLocalRing.residue W w)) ∧
      Module.finrank W W' = Module.finrank (IsLocalRing.ResidueField W) k ∧
      Finite (W' ≃ₐ[W] W') ∧
      (IsGalois (IsLocalRing.ResidueField W) k →
        Nat.card (W' ≃ₐ[W] W') = Module.finrank W W' ∧
        ∀ w' : W', (∀ γ : W' ≃ₐ[W] W', γ • w' = w') ↔ w' ∈ Set.range (algebraMap W W')) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_etale_dvr_residueField_equiv_card_algEquiv_eq_of_isAdicComplete.solution
