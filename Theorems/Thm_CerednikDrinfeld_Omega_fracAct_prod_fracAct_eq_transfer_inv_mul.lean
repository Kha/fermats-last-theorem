import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Mathlib.GroupTheory.Transfer
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_fracAct_prod_fracAct_eq_transfer_inv_mul

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Omega.fracAct_prod_fracAct_eq_transfer_inv_mul
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    (Γ' : Subgroup G) [Γ'.FiniteIndex] [Fintype (G ⧸ Γ')] (s : G ⧸ Γ' → G) (hs : ∀ q : G ⧸ Γ', (QuotientGroup.mk (s q) : G ⧸ Γ') = q)
    (f : merField ϖ) (χ : ↥Γ' →* Kˣ)
    (hf : ∀ γ : ↥Γ', Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ γ) f =
      algebraMap K (merField ϖ) (((χ γ)⁻¹ : Kˣ) : K) * f) :
    ∀ γ : G, Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ γ)
        (∏ q : G ⧸ Γ', Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ (s q)) f) =
      algebraMap K (merField ϖ) (((MonoidHom.transfer χ γ)⁻¹ : Kˣ) : K) *
        ∏ q : G ⧸ Γ', Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ (s q)) f := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_fracAct_prod_fracAct_eq_transfer_inv_mul.solution
