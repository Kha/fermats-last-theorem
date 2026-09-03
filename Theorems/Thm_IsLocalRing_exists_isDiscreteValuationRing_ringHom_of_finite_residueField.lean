import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_isDiscreteValuationRing_ringHom_of_finite_residueField
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

universe u

theorem IsLocalRing.exists_isDiscreteValuationRing_ringHom_of_finite_residueField
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A)
    (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    [IsAdicComplete (IsLocalRing.maximalIdeal S) S] [Algebra A S] [IsLocalHom (algebraMap A S)]
    [Finite (IsLocalRing.ResidueField S)] :
    ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : A →+* W)
      (_ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ}) (τ : W →+* S),
      IsLocalHom τ ∧ Function.Surjective ((IsLocalRing.residue S).comp τ) ∧ τ.comp σ = algebraMap A S := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_isDiscreteValuationRing_ringHom_of_finite_residueField.solution
