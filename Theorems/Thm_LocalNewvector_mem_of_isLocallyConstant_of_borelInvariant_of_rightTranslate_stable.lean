import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import P2M.Util
import P2M.Sol.S_LocalNewvector_mem_of_isLocallyConstant_of_borelInvariant_of_rightTranslate_stable
attribute [-instance] FLT.SpectralSide.instCompactSpaceMatrix
attribute [-simp] LocalNewvector.unitValuation_apply LocalNewvector.valChar_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv

set_option autoImplicit false

theorem LocalNewvector.mem_of_isLocallyConstant_of_borelInvariant_of_rightTranslate_stable
    (p : ℕ) [Fact p.Prime] (S : Submodule ℂ (GL (Fin 2) ℚ_[p] → ℂ))
    (hS : ∀ (h : GL (Fin 2) ℚ_[p]), ∀ F ∈ S, (fun g => F (g * h)) ∈ S)
    (F₀ : GL (Fin 2) ℚ_[p] → ℂ) (hF₀S : F₀ ∈ S) (hF₀lc : IsLocallyConstant F₀)
    (hF₀B : ∀ b g : GL (Fin 2) ℚ_[p], (b : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 = 0 → F₀ (b * g) = F₀ g)
    (hF₀nc : ∃ g : GL (Fin 2) ℚ_[p], F₀ g ≠ F₀ 1)
    (F : GL (Fin 2) ℚ_[p] → ℂ) (hFlc : IsLocallyConstant F)
    (hFB : ∀ b g : GL (Fin 2) ℚ_[p], (b : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 = 0 → F (b * g) = F g) :
    F ∈ S := by p2m_exact_reverting @_root_.P2MW.S_LocalNewvector_mem_of_isLocallyConstant_of_borelInvariant_of_rightTranslate_stable.solution
