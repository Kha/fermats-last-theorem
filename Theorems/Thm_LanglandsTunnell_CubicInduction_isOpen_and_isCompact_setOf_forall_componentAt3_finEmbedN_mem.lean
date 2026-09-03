import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem

set_option autoImplicit false

open IsDedekindDomain
open scoped NumberField

theorem LanglandsTunnell.CubicInduction.isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (hopen : ∀ p, IsOpen (K' p : Set (LocalGL3 p))) (hcpt : ∀ p, IsCompact (K' p : Set (LocalGL3 p)))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    IsOpen {k : Matrix.GeneralLinearGroup (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) |
        ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} ∧
      IsCompact {k : Matrix.GeneralLinearGroup (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) |
        ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem.solution
