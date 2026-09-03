import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_isNicePinned_sPart_shift

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.Converse.isNicePinned_sPart_shift (K : Type) [Field K] [NumberField K]
    {ι : Type} (D : LanglandsTunnell.LDatum ι) (hc : D.center = 1 / 2)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (A Ad : (↥S → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (ε : ℂ) (N : ℝ) (k : ↥S → ℤ)
    (h : IsNicePinned D (sPart K S A μ) (sPartDual K S Ad μ) ε N) :
    IsNicePinned D (sPart K S (fun n => A (n - k)) μ) (sPartDual K S (fun n => Ad (n + k)) μ) ε N := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_isNicePinned_sPart_shift.solution
