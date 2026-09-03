import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import P2M.Util
import P2M.Sol.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
attribute [-instance] instCountableOfNumberField_definitions

theorem NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
    (F : Type) [Field F] [NumberField F]
    (a : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ)
    (ha : (a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F).2 = 1) :
    (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) a : ℝ)
      = ∏ w : NumberField.InfinitePlace F,
          ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F).1 w‖ ^ w.mult := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one.solution
