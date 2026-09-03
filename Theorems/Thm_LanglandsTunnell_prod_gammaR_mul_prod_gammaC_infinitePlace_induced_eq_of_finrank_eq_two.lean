import Mathlib
import Definitions.Def_LanglandsTunnell_ArchParam
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_prod_gammaR_mul_prod_gammaC_infinitePlace_induced_eq_of_finrank_eq_two

set_option autoImplicit false

open NumberField Complex LanglandsTunnell

open scoped Classical in

theorem LanglandsTunnell.prod_gammaR_mul_prod_gammaC_infinitePlace_induced_eq_of_finrank_eq_two
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (U : ∀ w : InfinitePlace E, w.IsReal → ℂ) (a : ∀ w : InfinitePlace E, w.IsReal → ZMod 2)
    (V : ∀ w : InfinitePlace E, w.IsComplex → ℂ) (k : ∀ w : InfinitePlace E, w.IsComplex → ℤ)
    (U' : ∀ w' : InfinitePlace M, w'.IsReal → ℂ) (a' : ∀ w' : InfinitePlace M, w'.IsReal → ZMod 2)
    (V' : ∀ w' : InfinitePlace M, w'.IsComplex → ℂ) (k' : ∀ w' : InfinitePlace M, w'.IsComplex → ℤ)
    (d : ∀ w' : InfinitePlace M, w'.IsReal → ZMod 2)
    (hd : ∀ (w₁ w₂ : InfinitePlace M) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal), w₁ ≠ w₂ →
      w₁.comap (algebraMap E M) = w₂.comap (algebraMap E M) → d w₁ h₁ + d w₂ h₂ = 1)
    (hU' : ∀ w', ∀ hw' : w'.IsReal,
      U' w' hw' = U (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M)))
    (ha' : ∀ w', ∀ hw' : w'.IsReal,
      a' w' hw' = a (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M)) + d w' hw')
    (hV' : ∀ w', ∀ hw' : w'.IsComplex,
      V' w' hw' = if h : (w'.comap (algebraMap E M)).IsReal then U _ h
        else V _ (InfinitePlace.not_isReal_iff_isComplex.mp h))
    (hk' : ∀ w', ∀ hw' : w'.IsComplex,
      (k' w' hw').natAbs = if h : (w'.comap (algebraMap E M)).IsReal then 0
        else (k _ (InfinitePlace.not_isReal_iff_isComplex.mp h)).natAbs)
    (s : ℂ) :
    (∏ w' : {w' : InfinitePlace M // w'.IsReal},
        Gammaℝ (s + (U' w'.1 w'.2 + signShift (a' w'.1 w'.2)))) *
      ∏ w' : {w' : InfinitePlace M // w'.IsComplex},
        Gammaℂ (s + (V' w'.1 w'.2 + ((k' w'.1 w'.2).natAbs : ℂ) / 2)) =
    (∏ w : {w : InfinitePlace E // w.IsReal},
        Gammaℝ (s + (U w.1 w.2 + signShift (a w.1 w.2))) *
          Gammaℝ (s + (U w.1 w.2 + signShift (1 + a w.1 w.2)))) *
      ∏ w : {w : InfinitePlace E // w.IsComplex},
        Gammaℂ (s + (V w.1 w.2 + ((k w.1 w.2).natAbs : ℂ) / 2)) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_prod_gammaR_mul_prod_gammaC_infinitePlace_induced_eq_of_finrank_eq_two.solution
