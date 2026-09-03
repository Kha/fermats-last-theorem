import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_forall_jacquetTruncated3_cellSectionOf_twistFamily_eq_finsum
attribute [-simp] LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

open scoped Classical

theorem LanglandsTunnell.CubicInduction.exists_forall_jacquetTruncated3_cellSectionOf_twistFamily_eq_finsum
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))

    (n : Fin 3 → ℤ)
    (lamU : ℂ → Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hlamU : ∀ (u : ℂ) (i : Fin 3) (a : (p.adicCompletion ℚ)ˣ),
      ((lamU u i a : ℂˣ) : ℂ) = ((lam i a : ℂˣ) : ℂ) * ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ ((n i : ℂ) * u))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (g : LocalGL3 p) (c : ℤ) :
    ∃ e : ℤ → ℂ, {i : ℤ | e i ≠ 0}.Finite ∧
      ∀ u : ℂ, jacquetTruncated3 p c (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf p (lamU u) Φ)) =
        ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * e i := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_jacquetTruncated3_cellSectionOf_twistFamily_eq_finsum.solution
