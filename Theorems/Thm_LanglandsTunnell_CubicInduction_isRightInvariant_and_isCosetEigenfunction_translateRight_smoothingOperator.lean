import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator

set_option autoImplicit false
open Matrix IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator
    (p : HeightOneSpectrum (𝓞 ℚ)) (lam1 lam2 : ℂ)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hφ : SlabL2.IsSmoothingKernel φ)
    (_hφp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, φ g ≠ 0 → componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) (_hh : componentAt3 (𝓞 ℚ) ℚ p h = 1)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hc : Continuous f)
    (_hK : IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (_hT1 : IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) f lam1)
    (_hT2 : IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) f lam2) :
    IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (SlabL2.translateRight h (SlabL2.smoothingOperator φ f)) ∧
    IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) (SlabL2.translateRight h (SlabL2.smoothingOperator φ f)) lam1 ∧
    IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) (SlabL2.translateRight h (SlabL2.smoothingOperator φ f)) lam2 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator.solution
