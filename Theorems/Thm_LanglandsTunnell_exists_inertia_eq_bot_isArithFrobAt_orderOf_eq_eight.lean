import Mathlib
import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_FormalBaseChange
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_inertia_eq_bot_isArithFrobAt_orderOf_eq_eight
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false
open NumberField IsDedekindDomain AutomorphicForm LanglandsTunnell

theorem LanglandsTunnell.exists_inertia_eq_bot_isArithFrobAt_orderOf_eq_eight
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S ∧ ∃ (Q : Ideal (𝓞 L)) (σ : L ≃ₐ[ℚ] L),
      Q.IsMaximal ∧ Q.under (𝓞 ℚ) = v.asIdeal ∧ Q.inertia (L ≃ₐ[ℚ] L) = ⊥ ∧ IsArithFrobAt (𝓞 ℚ) σ Q ∧
        orderOf (e σ) = 8 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_inertia_eq_bot_isArithFrobAt_orderOf_eq_eight.solution
