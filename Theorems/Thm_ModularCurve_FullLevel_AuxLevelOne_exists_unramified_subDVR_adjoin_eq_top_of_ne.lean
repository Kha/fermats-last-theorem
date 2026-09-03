import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_AuxLevelOne_exists_unramified_subDVR_adjoin_eq_top_of_ne

set_option autoImplicit false

theorem ModularCurve.FullLevel.AuxLevelOne.exists_unramified_subDVR_adjoin_eq_top_of_ne
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (ζA : A) (hζA : algebraMap A L ζA = ζ)
    (K : Type) [CommRing K] [Algebra A K] :
    ∃ (A₀ : Type) (_ : CommRing A₀) (_ : IsDomain A₀) (_ : IsDiscreteValuationRing A₀)
      (_ : Algebra A₀ A) (_ : Algebra A₀ K) (_ : IsScalarTower A₀ A K),
      IsLocalRing.maximalIdeal A₀ = Ideal.span {(q : A₀)} ∧
      Finite (IsLocalRing.ResidueField A₀) ∧
      Function.Injective (algebraMap A₀ A) ∧ Module.Finite A₀ A ∧
      IsUnit ((ℓ : ℕ) : A₀) ∧ IsUnit ((M' : ℕ) : A₀) ∧
      (∃ ω : A₀, IsPrimitiveRoot ω ℓ) ∧
      Algebra.adjoin A₀ {ζA} = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_unramified_subDVR_adjoin_eq_top_of_ne.solution
