import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_eq_algebraMap_of_forall_taylorCoeff_mul_pow_eq_zero_of_generalPosition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve open ModularCurve hiding exists_eq_algebraMap_of_hasValue_smul_of_generalPosition

theorem ModularCurve.exists_eq_algebraMap_of_forall_taylorCoeff_mul_pow_eq_zero_of_generalPosition
    {k : Type*} [Field k] {N : ℕ} [NeZero N]
    (g : SemilinearAut k ↥(modularFunctionFieldC k N))
    (W E₁ E₂ : Finset (Place k ↥(modularFunctionFieldC k N)))
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ E₁ → 0 ≤ v.ord h) → (∀ v ∈ E₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ E₂ → 0 ≤ v.ord h) → (∀ v ∈ E₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k N) c)
    (t : Place k ↥(modularFunctionFieldC k N) → ↥(modularFunctionFieldC k N))
    (ht₁ : ∀ v ∈ E₁, v.ord (t v) = 1) (ht₂ : ∀ v ∈ E₂, v.ord (t v) = 1)
    (hrat₁ : ∀ v ∈ E₁, v.IsRational) (hrat₂ : ∀ v ∈ E₂, v.IsRational)
    (m : ℕ) (h₁ h₂ : ↥(modularFunctionFieldC k N))
    (hh₁ : ∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ E₁ → 0 ≤ v.ord h₁) (hh₁' : ∀ v ∈ E₁, -(m : ℤ) ≤ v.ord h₁)
    (hh₂ : ∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ E₂ → 0 ≤ v.ord h₂) (hh₂' : ∀ v ∈ E₂, -(m : ℤ) ≤ v.ord h₂)
    (hval : ∀ w ∈ W, ∃ c : k, w.HasValue h₁ c ∧ (g • w).HasValue h₂ c)
    (hpol₁ : ∀ v ∈ E₁, ∀ r : ℕ, r + 1 < m → Place.taylorCoeff v (t v) r (h₁ * t v ^ m) = 0)
    (hpol₂ : ∀ v ∈ E₂, ∀ r : ℕ, r + 1 < m → Place.taylorCoeff v (t v) r (h₂ * t v ^ m) = 0) :
    ∃ c : k, h₁ = algebraMap k ↥(modularFunctionFieldC k N) c ∧
      h₂ = algebraMap k ↥(modularFunctionFieldC k N) c := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_eq_algebraMap_of_forall_taylorCoeff_mul_pow_eq_zero_of_generalPosition.solution
