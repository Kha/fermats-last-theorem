import Definitions.Def_LanglandsTunnell_ArchBaseChange
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_prod_map_Gamma_twistedGamma_and_dual_and_archRootNumber_discrete_one_real_one_complex

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse

open scoped Classical in

theorem LanglandsTunnell.Converse.prod_map_Gamma_twistedGamma_and_dual_and_archRootNumber_discrete_one_real_one_complex
    (K : Type) [Field K] [NumberField K]
    (w₀ wC : NumberField.InfinitePlace K) (h₀ : w₀.IsReal) (hC : wC.IsComplex)
    (hall : ∀ w : NumberField.InfinitePlace K, w = wC ∨ w = w₀)
    (uR : ∀ w : NumberField.InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : NumberField.InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : NumberField.InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : NumberField.InfinitePlace K, w.IsComplex → ℤ)
    (P : RealArchParam) (uP : ℂ) (nP : ℕ) (hnP : 1 ≤ nP) (hP : P = RealArchParam.discrete uP nP hnP)
    (s : ℂ) :
    (((twistedGammaR K (archOfParamR K P) uR aR).map fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod = 1) ∧
    (((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod =
        Complex.Gammaℂ (s + 1 / 2 + ((uP + uR w₀ h₀) + (nP : ℂ) / 2)) *
        (Complex.Gammaℂ (s + 1 / 2 + ((uP + uC wC hC) + ((((nP : ℤ) + kC wC hC).natAbs : ℕ) : ℂ) / 2)) *
        Complex.Gammaℂ (s + 1 / 2 + ((uP + uC wC hC) + (((-(nP : ℤ) + kC wC hC).natAbs : ℕ) : ℂ) / 2)))) ∧
    (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
          fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod = 1) ∧
    (((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
          fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod =
        Complex.Gammaℂ (s + 1 / 2 + ((-uP + -uR w₀ h₀) + (nP : ℂ) / 2)) *
        (Complex.Gammaℂ (s + 1 / 2 + ((-uP + -uC wC hC) + ((((nP : ℤ) + kC wC hC).natAbs : ℕ) : ℂ) / 2)) *
        Complex.Gammaℂ (s + 1 / 2 + ((-uP + -uC wC hC) + (((-(nP : ℤ) + kC wC hC).natAbs : ℕ) : ℂ) / 2)))) ∧
    (archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val *
          (-1 : ℂ) ^ (Finset.univ : Finset {w : NumberField.InfinitePlace K // w.IsComplex}).card =
        Complex.I ^ (nP + 1) *
          (Complex.I ^ ((nP : ℤ) + kC wC hC).natAbs * Complex.I ^ (-(nP : ℤ) + kC wC hC).natAbs) *
          (-1 : ℂ) ^ (nP + 1) * (-1 : ℂ) ^ 1) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_prod_map_Gamma_twistedGamma_and_dual_and_archRootNumber_discrete_one_real_one_complex.solution
