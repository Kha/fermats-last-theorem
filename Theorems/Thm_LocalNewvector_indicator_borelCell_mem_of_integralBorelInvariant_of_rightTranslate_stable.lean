import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import P2M.Util
import P2M.Sol.S_LocalNewvector_indicator_borelCell_mem_of_integralBorelInvariant_of_rightTranslate_stable
attribute [-instance] FLT.SpectralSide.instCompactSpaceMatrix
attribute [-simp] LocalNewvector.unitValuation_apply LocalNewvector.valChar_apply

set_option autoImplicit false

theorem LocalNewvector.indicator_borelCell_mem_of_integralBorelInvariant_of_rightTranslate_stable
    (p : ℕ) [Fact p.Prime] (S : Submodule ℂ (GL (Fin 2) ℚ_[p] → ℂ))
    (hS : ∀ (h : GL (Fin 2) ℚ_[p]), ∀ F ∈ S, (fun g => F (g * h)) ∈ S)
    (Φ : GL (Fin 2) ℚ_[p] → ℂ) (hΦS : Φ ∈ S)
    (hΦB : ∀ b g : GL (Fin 2) ℚ_[p], (b : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 = 0 → Φ (b * g) = Φ g)
    {L : ℕ} (hL : 1 ≤ L)
    (hΦK : ∀ m ∈ FLT.SmoothVectors.gl2CongruenceSubgroup p L, (fun g => Φ (g * m)) = Φ)
    (hΦN : ∀ x : ℚ_[p], ‖x‖ ≤ 1 → (fun g => Φ (g * LocalNewvector.borelElem p 1 1 x)) = Φ)
    (hΦT : ∀ a : ℚ_[p]ˣ, ‖(a : ℚ_[p])‖ = 1 →
      (fun g => Φ (g * LocalNewvector.borelElem p a 1 0)) = Φ)
    (hΦnc : ∃ g : GL (Fin 2) ℚ_[p], Φ g ≠ Φ 1) (M : ℕ) (hM : 2 ≤ M) :
    Set.indicator {g : GL (Fin 2) ℚ_[p] | ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0‖
        ≤ (p : ℝ) ^ (-(M : ℤ)) * ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1‖} 1 ∈ S := by p2m_exact_reverting @_root_.P2MW.S_LocalNewvector_indicator_borelCell_mem_of_integralBorelInvariant_of_rightTranslate_stable.solution
