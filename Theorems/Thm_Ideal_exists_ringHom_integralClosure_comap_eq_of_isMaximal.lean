import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Data.Complex.Basic
import P2M.Util
import P2M.Sol.S_Ideal_exists_ringHom_integralClosure_comap_eq_of_isMaximal

theorem Ideal.exists_ringHom_integralClosure_comap_eq_of_isMaximal {T : Type*} [CommRing T] [IsAddTorsionFree T] [Module.Finite ℤ T] (𝔪 : Ideal T) (h𝔪 : 𝔪.IsMaximal) : ∃ (f : T →+* integralClosure ℤ ℂ) (𝔐 : Ideal (integralClosure ℤ ℂ)), 𝔐.IsMaximal ∧ 𝔐.comap f = 𝔪 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_ringHom_integralClosure_comap_eq_of_isMaximal.solution
