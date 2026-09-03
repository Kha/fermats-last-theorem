import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_Measure_gram_trace_matrix_smul_map_volume_eq_pow_smul_map_of_pi_pi

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.Measure.gram_trace_matrix_smul_map_volume_eq_pow_smul_map_of_pi_pi
    (R : Type) [NormedCommRing R] [NormedAlgebra ℝ R] [MeasurableSpace R] [BorelSpace R]
    (ι : Type) [Fintype ι] [MeasurableSpace (Matrix ι ι R)] [BorelSpace (Matrix ι ι R)]
    (m : ℕ) (b : Fin m → R) (hb : LinearIndependent ℝ b) (hbsp : Submodule.span ℝ (Set.range b) = ⊤)
    (μ : Measure R) [SigmaFinite μ] (κ : ENNReal) (hκ : κ ≠ ⊤)
    (hμ : (ENNReal.ofReal (Real.sqrt |(Matrix.of fun a a' : Fin m =>
          Algebra.trace ℝ R (b a * b a')).det|)) •
        Measure.map (fun c : Fin m → ℝ => ∑ a, c a • b a) volume = κ • μ)
    (n : ℕ) (e : Fin n → Matrix ι ι R) (he : LinearIndependent ℝ e)
    (hesp : Submodule.span ℝ (Set.range e) = ⊤) :
    (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n =>
          Algebra.trace ℝ R (Matrix.trace (e i * e j))).det|)) •
        Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume =
      κ ^ (Fintype.card ι * Fintype.card ι) •
        Measure.map (Matrix.of : (ι → ι → R) → Matrix ι ι R)
          (Measure.pi fun _ : ι => Measure.pi fun _ : ι => μ) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_Measure_gram_trace_matrix_smul_map_volume_eq_pow_smul_map_of_pi_pi.solution
