import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.Fin.VecNotation
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two

theorem HopfAlgebra.prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two
    (p : ℕ) (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K] [Module.Flat ℤ K]
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgen : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = 2)
    (hK : ¬ Module.Finite ℤ K) :
    p.Prime ∧
    ∃ (K₀ : Type) (_ : CommRing K₀) (_ : HopfAlgebra ℤ K₀) (ψ : K₀ →ₐc[ℤ] K) (f : K₀),
      (letI : Algebra K₀ K := (ψ : K₀ →+* K).toAlgebra; IsLocalization.Away f K) ∧
      ((∃ e : K₀ ≃ₐ[ℤ] (Fin 2 → ℤ), e f = ![1, (p : ℤ)] ∧
          ∀ x : K₀, Bialgebra.counitAlgHom ℤ K₀ x = e x 0) ∨
       (p ≠ 2 ∧ ∃ e : K₀ ≃ₐc[ℤ] MonoidAlgebra ℤ (Multiplicative (ZMod 2)),
          e f = MonoidAlgebra.single 1 (((p : ℤ) + 1) / 2) +
            MonoidAlgebra.single (Multiplicative.ofAdd 1) ((1 - (p : ℤ)) / 2))) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two.solution
