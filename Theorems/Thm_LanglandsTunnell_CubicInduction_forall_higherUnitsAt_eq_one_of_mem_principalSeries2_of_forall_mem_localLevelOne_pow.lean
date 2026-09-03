import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_forall_higherUnitsAt_eq_one_of_mem_principalSeries2_of_forall_mem_localLevelOne_pow
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.forall_higherUnitsAt_eq_one_of_mem_principalSeries2_of_forall_mem_localLevelOne_pow
    (p : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (b : ℕ)
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ) (hf0 : f ≠ 0)
    (hfK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b),
      ∀ g : GL (Fin 2) (p.adicCompletion ℚ), f (g * k) = f g) :
    ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p b, χ i u = 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_forall_higherUnitsAt_eq_one_of_mem_principalSeries2_of_forall_mem_localLevelOne_pow.solution
