import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_isThetaPair_ordAt_eq_card

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld.Omega~finite_setOf_pmoebius_mem_affinoid"

theorem CerednikDrinfeld.Omega.exists_isThetaPair_ordAt_eq_card
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {a b z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) :
    ∃ F H : ↥(holRing ϖ), IsThetaPair ϖ ρ a b z₀ F H ∧
      ∀ z : ↥(upperHalfPlane K₀ K),
        ordAt ϖ F z = Nat.card {γ : G // pmoebius K₀ (ρ γ) a = (z : K)} ∧
        ordAt ϖ H z = Nat.card {γ : G // pmoebius K₀ (ρ γ) b = (z : K)} := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_isThetaPair_ordAt_eq_card.solution
