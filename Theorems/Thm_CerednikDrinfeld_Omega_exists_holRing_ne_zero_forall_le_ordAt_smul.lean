import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_holRing_ne_zero_forall_le_ordAt_smul

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega hiding isDomain_holRing finite_setOf_pmoebius_mem_affinoid ordAt_mul countable_of_isDiscrete exists_mem_upperHalfPlane_forall_pmoebius_ne_and_of_countable_of_archimedean exists_isThetaPair_ordAt_eq_card open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Omega.exists_holRing_ne_zero_forall_le_ordAt_smul
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {ι : Type} [Fintype ι] (b : ι → ↥(upperHalfPlane K₀ K)) (m : ι → ℕ) :
    ∃ H : ↥(holRing ϖ), H ≠ 0 ∧
      ∀ (i : ι) (γ : G), m i ≤ ordAt ϖ H (ρ γ • b i) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_holRing_ne_zero_forall_le_ordAt_smul.solution
