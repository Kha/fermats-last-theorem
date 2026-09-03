import Mathlib
import P2M.Util
import P2M.Sol.S_PadicInt_two_mul_finrank_iInf_ker_eq_finrank_of_isBaseChange_of_bilinForm_similitude

set_option autoImplicit false

theorem PadicInt.two_mul_finrank_iInf_ker_eq_finrank_of_isBaseChange_of_bilinForm_similitude
    (p : ℕ) [Fact p.Prime] {ι : Type*} {P : Type*} [AddCommGroup P] [Module ℤ_[p] P]
    [Module.Free ℤ_[p] P] [Module.Finite ℤ_[p] P]
    (s : ι → P →ₗ[ℤ_[p]] P) (a : ι → ℤ_[p]) (i₀ : ι)
    (hW₀ : ∀ x : P, s i₀ x - x ∈ ⨅ j, LinearMap.ker (s j - a j • LinearMap.id))
    (hi₀ : ¬ (p : ℤ_[p]) ∣ a i₀ - 1) (hu₀ : ¬ (p : ℤ_[p]) ∣ a i₀)
    {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]
    (j : P →ₗ[ℤ_[p]] V) (hj : IsBaseChange ℚ_[p] j)
    {V' : Type*} [AddCommGroup V'] [Module ℚ_[p] V'] [FiniteDimensional ℚ_[p] V']
    (jV : V →ₗ[ℚ_[p]] V') (hjV : Function.Injective jV)
    (e : V' →ₗ[ℚ_[p]] V') (he : ∀ v : V', e (e v) = e v) (hrange : LinearMap.range jV = LinearMap.range e)
    (B : LinearMap.BilinForm ℚ_[p] V') (halt : ∀ v : V', B v v = 0)
    (hB : ∀ v : V', (∀ w : V', B v w = 0) → v = 0)
    (hadj : ∀ x y : V', B (e x) y = B x (e y))
    (g : V' →ₗ[ℚ_[p]] V') (hg : ∀ x : P, g (jV (j x)) = jV (j (s i₀ x)))
    (hsim : ∀ x y : V', B (g x) (g y) = algebraMap ℤ_[p] ℚ_[p] (a i₀) * B x y) :
    2 * Module.finrank ℤ_[p] ↥(⨅ j, LinearMap.ker (s j - a j • LinearMap.id)) =
      Module.finrank ℤ_[p] P := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_two_mul_finrank_iInf_ker_eq_finrank_of_isBaseChange_of_bilinForm_similitude.solution
