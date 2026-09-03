import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_HeckeTate_exists_archRootNumber_induced_of_finrank_eq_two

set_option autoImplicit false

open NumberField NumberField.TateGlobal NumberField.InfinitePlace LanglandsTunnell LanglandsTunnell.Converse
open scoped Classical in

theorem LanglandsTunnell.HeckeTate.exists_archRootNumber_induced_of_finrank_eq_two
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ)
    (hsign : ∀ w w' : InfinitePlace M, w ≠ w' → w.IsReal → w'.IsReal →
      w.comap (algebraMap E M) = w'.comap (algebraMap E M) →
      ((archLocalChar ξ w (-1) : ℂˣ) : ℂ) * archLocalChar ξ w' (-1) = -1) :
    ∃ c₀ : ℂ, c₀ ≠ 0 ∧
      ∀ (aR : ∀ w : InfinitePlace E, w.IsReal → ZMod 2) (kC : ∀ w : InfinitePlace E, w.IsComplex → ℤ)
        (aR' : ∀ w' : InfinitePlace M, w'.IsReal → ZMod 2)
        (kC' : ∀ w' : InfinitePlace M, w'.IsComplex → ℤ),
        (∀ w', ∀ hw' : w'.IsReal,
          ((archLocalChar ξ w' (-1) : ℂˣ) : ℂ) =
            (-1) ^ (aR' w' hw' - aR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M))).val) →
        (∀ w', ∀ hw' : w'.IsComplex,
          (kC' w' hw').natAbs = if h : (w'.comap (algebraMap E M)).IsReal then 0
            else (kC _ (InfinitePlace.not_isReal_iff_isComplex.mp h)).natAbs) →
        ∀ (uR : ∀ w : InfinitePlace E, w.IsReal → ℂ) (uC : ∀ w : InfinitePlace E, w.IsComplex → ℂ),
          ((Finset.univ : Finset {w' : InfinitePlace M // w'.IsReal}).prod
              fun w' => signEpsilon (aR' w'.1 w'.2)) *
            ((Finset.univ : Finset {w' : InfinitePlace M // w'.IsComplex}).prod
              fun w' => Complex.I ^ (kC' w'.1 w'.2).natAbs) =
          c₀ * archRootNumber E (fun _ _ => RealArchParam.oddArtin) (fun _ _ => ComplexArchParam.trivialArtin)
                uR aR uC kC := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_HeckeTate_exists_archRootNumber_induced_of_finrank_eq_two.solution
