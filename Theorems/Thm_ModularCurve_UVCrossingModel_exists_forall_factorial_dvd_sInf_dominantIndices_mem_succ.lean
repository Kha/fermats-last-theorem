import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_forall_factorial_dvd_sInf_dominantIndices_mem_succ

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem ModularCurve.UVCrossingModel.exists_forall_factorial_dvd_sInf_dominantIndices_mem_succ
    {W : Type u} [CommRing W] (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E : ℕ) (hE : 1 ≤ E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hne : ∃ n : ℤ, v (nfCoeff ab n) ≠ ⊤) :
    ∃ N : ℕ, ∀ r : ℕ, 1 ≤ r → Nat.factorial N ∣ r →
      (∀ S : ℕ, S + 1 ≤ r * E →
        sInf (dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) S ab) ∈
          dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) (S + 1) ab) ∧
      (∀ S : ℕ, 1 ≤ S → S ≤ r * E →
        sSup (dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) S ab) ∈
          dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) (S - 1) ab) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_forall_factorial_dvd_sInf_dominantIndices_mem_succ.solution
