import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_lintegral_mul_apply_col_det_eq_mul_lintegral_setLIntegral_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing

set_option autoImplicit false

open MeasureTheory NumberField
open scoped ENNReal

open scoped Classical in

theorem AutomorphicForm.lintegral_mul_apply_col_det_eq_mul_lintegral_setLIntegral_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing
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

    (F : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) → ENNReal)
    (hF : Measurable[borel _] F)
    (hF1 : ∀ᵐ g ∂τa,
      ∫⁻ y, F ((g * AutomorphicForm.unipotentGL2 ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y) :
            GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))
        ∂((2 : ENNReal) ^ NumberField.InfinitePlace.nrComplexPlaces K •
          (volume : Measure (mixedEmbedding.mixedSpace K))) = 1)
    (Ψ : (Fin 2 → mixedEmbedding.mixedSpace K) × mixedEmbedding.mixedSpace K → ENNReal)
    (hΨ : Measurable Ψ) :
    ∫⁻ g, F (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) *
        Ψ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace K
              ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i 0),
            InfiniteAdeleRing.ringEquiv_mixedSpace K
              ((Matrix.GeneralLinearGroup.det g : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) ∂τa =
      s * ∫⁻ c, ∫⁻ δ in {δ | IsUnit δ}, Ψ (c, δ) * (ENNReal.ofReal |Algebra.norm ℝ δ| ^ 2)⁻¹
          ∂((2 : ENNReal) ^ NumberField.InfinitePlace.nrComplexPlaces K •
            (volume : Measure (mixedEmbedding.mixedSpace K)))
        ∂(Measure.pi fun _ : Fin 2 =>
          (2 : ENNReal) ^ NumberField.InfinitePlace.nrComplexPlaces K •
            (volume : Measure (mixedEmbedding.mixedSpace K))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_lintegral_mul_apply_col_det_eq_mul_lintegral_setLIntegral_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing.solution
