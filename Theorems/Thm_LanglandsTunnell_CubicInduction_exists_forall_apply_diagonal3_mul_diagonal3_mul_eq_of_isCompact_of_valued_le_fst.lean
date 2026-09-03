import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst
    (v : HeightOneSpectrum (𝓞 ℚ))

    (W₀ : LocalGL3 v → ℂ)
    (hW₀law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W₀)
    (d : ℕ)
    (hW₀lev : ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
      (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
      ∀ g : LocalGL3 v, W₀ (g * k) = W₀ g)

    (C : Set (LocalGL3 v)) (hC : IsCompact C) :
    ∃ N : ℕ, ∀ X ∈ C, ∀ a : Fin 3 → (v.adicCompletion ℚ)ˣ,
      Valued.v (((a 0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) / ((a 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) ≤
        WithZero.exp (-(N : ℤ)) →
      ∀ s t : (v.adicCompletion ℚ)ˣ, s ∈ higherUnitsAt ℚ v d → t ∈ higherUnitsAt ℚ v d →
        W₀ (diagonal3 v a * diagonal3 v ![s, t, t] * X) = W₀ (diagonal3 v a * X) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst.solution
