import Mathlib
import Definitions.Def_ModularCurve_HpoolLevelRing
import P2M.Util
import P2M.Sol.S_ModularCurve_HpoolLevelRing_noZeroSMulDivisors_levelRing_of_forall_isPrime

set_option autoImplicit false

open Polynomial ModularCurve ModularCurve.HpoolLevelRing

theorem ModularCurve.HpoolLevelRing.noZeroSMulDivisors_levelRing_of_forall_isPrime
    (p : ℕ) [Fact p.Prime] (f : ℤ) (hf : f ≠ 0) (hpf : (p : ℤ) ∣ f) (u : Afin p) (g : ℤ[X])
    (hprime : ∀ q : ℕ, q.Prime → q ≠ p → (Ideal.span {((q : ℕ) : Afin p)}).IsPrime)
    (hne : ∀ q : ℕ, q.Prime → q ≠ p → (Polynomial.aeval (R := ℤ) u g : Afin p) ∉ Ideal.span {((q : ℕ) : Afin p)}) :
    NoZeroSMulDivisors (Localization.Away f) (levelRing p f u g) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_HpoolLevelRing_noZeroSMulDivisors_levelRing_of_forall_isPrime.solution
