import Definitions.Def_NumberField_AdelicFourier
import Mathlib.Algebra.Module.ZLattice.Summable
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_summable_norm_schwartzMap_ringOfIntegers_translate

open NumberField NumberField.mixedEmbedding
open scoped SchwartzMap Classical

noncomputable section
theorem NumberField.mixedEmbedding.summable_norm_schwartzMap_ringOfIntegers_translate
    (F : Type*) [Field F] [NumberField F]
    (g : 𝓢(NumberField.mixedEmbedding.mixedSpace F, ℂ))
    (x : NumberField.mixedEmbedding.mixedSpace F) :
    Summable fun a : 𝓞 F => ‖g (x + NumberField.mixedEmbedding F (a : F))‖ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_summable_norm_schwartzMap_ringOfIntegers_translate.solution
