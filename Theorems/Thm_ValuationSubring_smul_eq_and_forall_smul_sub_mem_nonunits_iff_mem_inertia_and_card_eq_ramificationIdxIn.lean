import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_smul_eq_and_forall_smul_sub_mem_nonunits_iff_mem_inertia_and_card_eq_ramificationIdxIn

set_option autoImplicit false

open scoped Pointwise

theorem ValuationSubring.smul_eq_and_forall_smul_sub_mem_nonunits_iff_mem_inertia_and_card_eq_ramificationIdxIn
    {R S F : Type*} [CommRing R] [CommRing S] [Field F] [Algebra R S] [Algebra S F] [IsFractionRing S F]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [MulSemiringAction G F]
    (hGSF : ∀ (g : G) (s : S), g • algebraMap S F s = algebraMap S F (g • s))
    (𝔓 : Ideal S) (P : ValuationSubring F)
    (hSP : ∀ s : S, algebraMap S F s ∈ P)
    (hcent : ∀ s : S, algebraMap S F s ∈ P.nonunits ↔ s ∈ 𝔓)
    (hfrac : ∀ e : ↥P, ∃ s t : S, t ∉ 𝔓 ∧ (e : F) * algebraMap S F t = algebraMap S F s) :
    (∀ g : G, (g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits) ↔ g ∈ 𝔓.inertia G) ∧
    (∀ [IsGaloisGroup G R S] [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S]
        [Module.IsTorsionFree R S] (p : Ideal R) [𝔓.LiesOver p] [𝔓.IsMaximal]
        [Algebra.IsSeparable (R ⧸ p) (S ⧸ 𝔓)], p ≠ ⊥ →
      Nat.card {g : G // g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits} = p.ramificationIdxIn S) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_smul_eq_and_forall_smul_sub_mem_nonunits_iff_mem_inertia_and_card_eq_ramificationIdxIn.solution
