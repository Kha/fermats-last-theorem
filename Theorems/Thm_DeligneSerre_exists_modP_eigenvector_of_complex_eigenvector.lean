import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import P2M.Util
import P2M.Sol.S_DeligneSerre_exists_modP_eigenvector_of_complex_eigenvector

set_option autoImplicit false

open scoped Matrix

theorem DeligneSerre.exists_modP_eigenvector_of_complex_eigenvector
    {t : ℕ} {I : Type*} (A : I → Matrix (Fin t) (Fin t) ℤ)
    {p : ℕ} [Fact p.Prime]
    {𝔪 : Ideal (integralClosure ℤ ℂ)} (hmax : 𝔪.IsPrime)
    (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    {α : I → integralClosure ℤ ℂ} {v : Fin t → ℂ} (hv : v ≠ 0)
    (heig : ∀ i, ((A i).map (Int.cast : ℤ → ℂ)).mulVec v = ((α i : ℂ) • v))
    {n : I → ℤ} (hcong : ∀ i, α i - (n i : integralClosure ℤ ℂ) ∈ 𝔪) :
    ∃ m : Fin t → ZMod p, m ≠ 0 ∧
      ∀ i, ((A i).map (Int.cast : ℤ → ZMod p)).mulVec m = ((n i : ZMod p) • m) := by p2m_exact_reverting @_root_.P2MW.S_DeligneSerre_exists_modP_eigenvector_of_complex_eigenvector.solution
