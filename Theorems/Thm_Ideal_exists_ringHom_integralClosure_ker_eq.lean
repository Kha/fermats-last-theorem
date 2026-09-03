import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Data.Complex.Basic
import P2M.Util
import P2M.Sol.S_Ideal_exists_ringHom_integralClosure_ker_eq

theorem Ideal.exists_ringHom_integralClosure_ker_eq {T : Type*} [CommRing T] [Module.Finite ℤ T] (𝔓 : Ideal T) (h𝔓 : 𝔓.IsPrime) (hint : ∀ n : ℤ, (n : T) ∈ 𝔓 → n = 0) : ∃ f : T →+* integralClosure ℤ ℂ, RingHom.ker f = 𝔓 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_ringHom_integralClosure_ker_eq.solution
