import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_Measure_map_withDensity_gram_trace_matrix_pi_eq_pi_of_span_eq

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.Measure.map_withDensity_gram_trace_matrix_pi_eq_pi_of_span_eq
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : ι → Type) [∀ i, CommRing (E i)] [∀ i, Algebra ℝ (E i)] [∀ i, Module.Free ℝ (E i)]
    [∀ i, Module.Finite ℝ (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, IsTopologicalRing (E i)]
    [∀ i, ContinuousSMul ℝ (E i)] [∀ i, T2Space (E i)]
    [∀ i, MeasurableSpace (Matrix (Fin 2) (Fin 2) (E i))] [∀ i, BorelSpace (Matrix (Fin 2) (Fin 2) (E i))]
    [MeasurableSpace (Matrix (Fin 2) (Fin 2) ((i : ι) → E i))] [BorelSpace (Matrix (Fin 2) (Fin 2) ((i : ι) → E i))]
    (W : ∀ i, Submodule ℝ (Matrix (Fin 2) (Fin 2) (E i)))
    (n : ι → ℕ) (e : ∀ i, Fin (n i) → Matrix (Fin 2) (Fin 2) (E i))
    (he : ∀ i, LinearIndependent ℝ (e i) ∧ Submodule.span ℝ (Set.range (e i)) = W i)
    (hW : ∀ i, ∃ X ∈ W i, Algebra.norm ℝ (Matrix.det X) ≠ 0)
    (W' : Submodule ℝ (Matrix (Fin 2) (Fin 2) ((i : ι) → E i)))
    (hW' : ∀ X : Matrix (Fin 2) (Fin 2) ((i : ι) → E i), X ∈ W' ↔ ∀ i, X.map (Pi.evalRingHom E i) ∈ W i)
    (N : ℕ) (f : Fin N → Matrix (Fin 2) (Fin 2) ((i : ι) → E i))
    (hf : LinearIndependent ℝ f ∧ Submodule.span ℝ (Set.range f) = W') :
    Measure.map (fun X : Matrix (Fin 2) (Fin 2) ((i : ι) → E i) => fun i : ι => X.map (Pi.evalRingHom E i))
        (((ENNReal.ofReal (Real.sqrt |(Matrix.of fun a b : Fin N =>
              Algebra.trace ℝ ((i : ι) → E i) (Matrix.trace (f a * f b))).det|)) •
            Measure.map (fun c : Fin N → ℝ => ∑ a, c a • f a) volume).withDensity
          fun X : Matrix (Fin 2) (Fin 2) ((i : ι) → E i) => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) =
      Measure.pi (fun i : ι =>
        ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun a b : Fin (n i) =>
              Algebra.trace ℝ (E i) (Matrix.trace (e i a * e i b))).det|)) •
            Measure.map (fun c : Fin (n i) → ℝ => ∑ a, c a • e i a) volume).withDensity
          fun X : Matrix (Fin 2) (Fin 2) (E i) => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_Measure_map_withDensity_gram_trace_matrix_pi_eq_pi_of_span_eq.solution
