import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_setLIntegral_ofReal_norm_det_eq_mul_two_pow_mul_two_pi_pow_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing

set_option autoImplicit false

open MeasureTheory NumberField
open scoped ENNReal

open scoped Classical in

theorem AutomorphicForm.setLIntegral_ofReal_norm_det_eq_mul_two_pow_mul_two_pi_pow_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing
    (K : Type) [Field K] [NumberField K]
    (τa : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))

    (n : ℕ) (e : Fin n → Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) (s : ENNReal)
    (harch :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := borel _
      letI := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
      LinearIndependent ℝ e ∧
        Submodule.span ℝ (Set.range e) = ⊤ ∧
        Measure.map (fun t : GL (Fin 2) (InfiniteAdeleRing K) =>
            (t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) τa =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n =>
                  Algebra.trace ℝ (InfiniteAdeleRing K) (Matrix.trace (e i * e j))).det|)) •
                Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)| ^ 2)⁻¹))

    (y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) → mixedEmbedding.mixedSpace K)
    (hy : Measurable[borel _] y)
    (hy1 : ∀ (g : GL (Fin 2) (InfiniteAdeleRing K)) (x : InfiniteAdeleRing K),
      y ((g * AutomorphicForm.unipotentGL2 x : GL (Fin 2) (InfiniteAdeleRing K)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) =
        y (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) + InfiniteAdeleRing.ringEquiv_mixedSpace K x) :
    ∫⁻ g in {g : GL (Fin 2) (InfiniteAdeleRing K) |
        ((∀ w : {w : InfinitePlace K // w.IsReal},
              (y (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))).1 w ∈ Set.Icc (0 : ℝ) 1) ∧
            ∀ w : {w : InfinitePlace K // w.IsComplex},
              ((y (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))).2 w).re ∈ Set.Icc (0 : ℝ) 1 ∧
              ((y (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))).2 w).im ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ i : Fin 2,
          (∀ w : {w : InfinitePlace K // w.IsReal},
              (InfiniteAdeleRing.ringEquiv_mixedSpace K
                ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i 0)).1 w ∈ Set.Icc (0 : ℝ) 1) ∧
            ∀ w : {w : InfinitePlace K // w.IsComplex},
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K
                  ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i 0)).2 w).re ∈ Set.Icc (0 : ℝ) 1 ∧
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K
                  ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i 0)).2 w).im ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ w : InfinitePlace K,
          ‖((Matrix.GeneralLinearGroup.det g : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w‖ ∈
            Set.Icc (1 : ℝ) (Real.exp 1)},
      ENNReal.ofReal
        ‖((Matrix.GeneralLinearGroup.det g : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ ∂τa =
      s * (2 ^ (4 * NumberField.InfinitePlace.nrComplexPlaces K + NumberField.InfinitePlace.nrRealPlaces K) *
        ENNReal.ofReal ((2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_setLIntegral_ofReal_norm_det_eq_mul_two_pow_mul_two_pi_pow_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing.solution
