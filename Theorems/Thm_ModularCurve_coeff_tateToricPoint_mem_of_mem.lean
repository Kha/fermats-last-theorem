import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPCusps
import P2M.Util
import P2M.Sol.S_ModularCurve_coeff_tateToricPoint_mem_of_mem

set_option autoImplicit false

theorem ModularCurve.coeff_tateToricPoint_mem_of_mem
    (R : Type*) [CommRing R] (p : ℕ) (B : Subring R) (c : Rˣ) (hc : (c : R) ∈ B) (hc' : ((c⁻¹ : Rˣ) : R) ∈ B) :
    (∀ m : ℕ, 0 < m → ((ModularCurve.tateToricPoint R p c).1.coeff (m : ℤ) ∈ B ∧
      (ModularCurve.tateToricPoint R p c).2.coeff (m : ℤ) ∈ B)) ∧
    (ModularCurve.tateToricPoint R p c).1.coeff 0 = (c : R) * Ring.inverse (1 - (c : R)) ^ 2 ∧
    (ModularCurve.tateToricPoint R p c).2.coeff 0 = (c : R) ^ 2 * Ring.inverse (1 - (c : R)) ^ 3 ∧
    (∀ k : ℤ, k < 0 → (ModularCurve.tateToricPoint R p c).1.coeff k = 0 ∧ (ModularCurve.tateToricPoint R p c).2.coeff k = 0) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeff_tateToricPoint_mem_of_mem.solution
