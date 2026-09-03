import Definitions.Def_NumberField_AdelicFourier
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_map_ringEquiv_mixedSpace_pi_eq_volume

set_option autoImplicit false

open NumberField NumberField.InfinitePlace MeasureTheory IsDedekindDomain
open scoped Classical in

theorem NumberField.AdelicFourier.map_ringEquiv_mixedSpace_pi_eq_volume
    (F : Type) [Field F] [NumberField F]
    [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)] :
    Measure.map (fun y : (∀ w : InfinitePlace F, w.Completion) ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F y)
        (Measure.pi fun w : InfinitePlace F ↦
          if hw : w.IsReal then Measure.map (Completion.ringEquivRealOfIsReal hw).symm volume
          else Measure.map (Completion.ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm volume)
      = (volume : Measure (mixedEmbedding.mixedSpace F)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_map_ringEquiv_mixedSpace_pi_eq_volume.solution
