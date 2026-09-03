import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Derivation.Basic
import P2M.Util
import P2M.Sol.S_Algebra_trace_inv_mul_derivation_eq_inv_norm_mul_derivation_norm

theorem Algebra.trace_inv_mul_derivation_eq_inv_norm_mul_derivation_norm {R F F' : Type*} [CommRing R] [Field F] [Field F'] [Algebra R F] [Algebra R F'] [Algebra F F'] (d : Derivation R F F) (d' : Derivation R F' F') (hd : ∀ x : F, d' (algebraMap F F' x) = algebraMap F F' (d x)) (h : F') : Algebra.trace F F' (h⁻¹ * d' h) = (Algebra.norm F h)⁻¹ * d (Algebra.norm F h) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_trace_inv_mul_derivation_eq_inv_norm_mul_derivation_norm.solution
