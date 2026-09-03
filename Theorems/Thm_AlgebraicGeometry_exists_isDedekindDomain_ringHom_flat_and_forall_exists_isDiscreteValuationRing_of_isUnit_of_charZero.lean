import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isDedekindDomain_ringHom_flat_and_forall_exists_isDiscreteValuationRing_of_isUnit_of_charZero

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.exists_isDedekindDomain_ringHom_flat_and_forall_exists_isDiscreteValuationRing_of_isUnit_of_charZero
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (n : ℕ) (hn : IsUnit ((n : ℕ) : 𝒪)) :
    ∃ (B₀ : Type) (_ : CommRing B₀) (_ : IsDedekindDomain B₀) (i : B₀ →+* 𝒪),
      Flat (Spec.map (CommRingCat.ofHom i)) ∧ IsUnit ((n : ℕ) : B₀) ∧
      (∀ 𝔭 : Ideal B₀, 𝔭.IsMaximal →
        ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
          (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (_ : IsAlgClosed (IsLocalRing.ResidueField W))
          (_ : Algebra B₀ W), Module.Flat B₀ W ∧ (IsLocalRing.maximalIdeal W).comap (algebraMap B₀ W) = 𝔭) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isDedekindDomain_ringHom_flat_and_forall_exists_isDiscreteValuationRing_of_isUnit_of_charZero.solution
