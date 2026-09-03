import Mathlib
import Definitions.Def_LanglandsTunnell_ExplicitLift
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_ExplicitLift_trace_det_eq_of_agreeUpToPartner_of_conjPow
attribute [-instance] LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

theorem LanglandsTunnell.ExplicitLift.trace_det_eq_of_agreeUpToPartner_of_conjPow
    {G : Type} [Group G] {F : Type} [Field F] [CharZero F]
    (ι : ℤ√(-2) →+* F)
    (M : G →* Matrix (Fin 2) (Fin 2) (ℤ√(-2)))
    (hM : ∀ g, M g ∈ Submonoid.closure
      ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2)))))
    (hMsurj : ∀ k ∈ Submonoid.closure
      ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2)))),
      ∃ g, M g = k)
    (r : G →* Matrix (Fin 2) (Fin 2) F)
    (hfin : ∀ g, IsOfFinOrder (r g))
    (S : Set G)
    (hS : ∀ φ ∈ S, (r φ).det = ι (M φ).det ∧
      ((r φ).trace = ι (M φ).trace ∨
        ((M φ).det = 1 ∧ ((M φ).trace = 1 ∨ (M φ).trace = -1) ∧
          (r φ).trace = -2 * ι (M φ).trace)))
    (hcover : ∀ σ : G, ∃ φ ∈ S, ∃ g : G, ∃ n : ℕ,
      r σ = r (g * φ ^ n * g⁻¹) ∧ M σ = M (g * φ ^ n * g⁻¹))
    (σ : G) :
    (r σ).trace = ι (M σ).trace ∧ (r σ).det = ι (M σ).det := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ExplicitLift_trace_det_eq_of_agreeUpToPartner_of_conjPow.solution
