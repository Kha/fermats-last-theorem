import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_smul_eq_and_forall_smul_sub_mem_nonunits_of_mem_inertia

set_option autoImplicit false

open scoped Pointwise

theorem ValuationSubring.smul_eq_and_forall_smul_sub_mem_nonunits_of_mem_inertia
    {B : Type*} [CommRing B] {F : Type*} [Field F] {G : Type*} [Group G]
    [MulSemiringAction G B] [MulSemiringAction G F]
    (ρ : B →+* F) (hρ : ∀ (g : G) (b : B), g • ρ b = ρ (g • b))
    (𝔶 : Ideal B) (P : ValuationSubring F)
    (hP : ∀ b : B, ρ b ∈ P) (hPy : ∀ b : B, ρ b ∈ P.nonunits ↔ b ∈ 𝔶)
    (huniq : ∀ P' : ValuationSubring F,
      (∀ b : B, ρ b ∈ P') → (∀ b : B, ρ b ∈ P'.nonunits ↔ b ∈ 𝔶) → P' = P)
    (hres : ∀ e : ↥P, ∃ b : B, (e : F) - ρ b ∈ P.nonunits)
    (g : G) (hg : g ∈ 𝔶.inertia G) :
    g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_smul_eq_and_forall_smul_sub_mem_nonunits_of_mem_inertia.solution
