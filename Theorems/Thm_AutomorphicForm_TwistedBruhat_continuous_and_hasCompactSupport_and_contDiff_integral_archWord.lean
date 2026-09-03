import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_TwistedBruhat_continuous_and_hasCompactSupport_and_contDiff_integral_archWord

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm

open scoped Classical in

theorem AutomorphicForm.TwistedBruhat.continuous_and_hasCompactSupport_and_contDiff_integral_archWord
    (L : Type) [Field L] [NumberField L]
    (A : InfiniteAdeleRing L ≃+* InfiniteAdeleRing L) (hA : Continuous A)
    (φ : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφ : IsArchTestFactor L φ)
    (ξ : (InfiniteAdeleRing L)ˣ → ℂ) (hξ : Continuous ξ)
    [MeasurableSpace (InfiniteAdeleRing L)ˣ] [BorelSpace (InfiniteAdeleRing L)ˣ]
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing L))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing L))]
    (μ : Measure ((InfiniteAdeleRing L)ˣ × GL (Fin 2) (InfiniteAdeleRing L) × (InfiniteAdeleRing L)ˣ))
    [IsFiniteMeasure μ]
    (K : Set ((InfiniteAdeleRing L)ˣ × GL (Fin 2) (InfiniteAdeleRing L) × (InfiniteAdeleRing L)ˣ))
    (hK : IsCompact K) (hμK : μ Kᶜ = 0) :
    Continuous (fun y : InfiniteAdeleRing L =>
        ∫ p, ξ p.2.2 * φ (p.2.1⁻¹ * unipotentGL2 (y * ((p.1⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L)) *
          diagOne (Units.map A.toRingHom.toMonoidHom p.1 * p.1⁻¹) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map A.toRingHom.toMonoidHom p.2.2) *
          Matrix.GeneralLinearGroup.map A.toRingHom p.2.1) ∂μ) ∧
    HasCompactSupport (fun y : InfiniteAdeleRing L =>
        ∫ p, ξ p.2.2 * φ (p.2.1⁻¹ * unipotentGL2 (y * ((p.1⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L)) *
          diagOne (Units.map A.toRingHom.toMonoidHom p.1 * p.1⁻¹) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map A.toRingHom.toMonoidHom p.2.2) *
          Matrix.GeneralLinearGroup.map A.toRingHom p.2.1) ∂μ) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun x : mixedEmbedding.mixedSpace L =>
        ∫ p, ξ p.2.2 * φ (p.2.1⁻¹ *
          unipotentGL2 ((InfiniteAdeleRing.ringEquiv_mixedSpace L).symm x * ((p.1⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L)) *
          diagOne (Units.map A.toRingHom.toMonoidHom p.1 * p.1⁻¹) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map A.toRingHom.toMonoidHom p.2.2) *
          Matrix.GeneralLinearGroup.map A.toRingHom p.2.1) ∂μ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_TwistedBruhat_continuous_and_hasCompactSupport_and_contDiff_integral_archWord.solution
