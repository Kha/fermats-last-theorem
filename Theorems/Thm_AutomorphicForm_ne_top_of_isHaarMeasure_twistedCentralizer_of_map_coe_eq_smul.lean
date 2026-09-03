import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_ne_top_of_isHaarMeasure_twistedCentralizer_of_map_coe_eq_smul

set_option autoImplicit false

open MeasureTheory NumberField
open scoped ENNReal TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

theorem AutomorphicForm.ne_top_of_isHaarMeasure_twistedCentralizer_of_map_coe_eq_smul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (τa : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)) (hτa : τa.IsHaarMeasure)
    (s : ℝ≥0∞) :
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
    ∀ ν : Measure (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
      Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
          ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τa =
        s • ν →
      s ≠ ⊤ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_ne_top_of_isHaarMeasure_twistedCentralizer_of_map_coe_eq_smul.solution
