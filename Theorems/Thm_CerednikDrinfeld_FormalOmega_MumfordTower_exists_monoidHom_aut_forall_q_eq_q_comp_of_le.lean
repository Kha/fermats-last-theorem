import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_monoidHom_aut_forall_q_eq_q_comp_of_le

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordTower.exists_monoidHom_aut_forall_q_eq_q_comp_of_le
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] (r : ℕ)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))
    (N : Subgroup (PGL(2, K₀))) (hNle : N ≤ Γ.map ρ) (hNnorm : (N.subgroupOf (Γ.map ρ)).Normal)
    (D : MumfordTower 𝒪 π K₀ r g₁ N) :
    ∃ act : ∀ n : ℕ, ↥Γ →* Aut (D.Z n),

      (∀ (n : ℕ) (γ : ↥Γ), (act n γ).hom ≫ D.zb n = D.zb n) ∧

      (∀ (n : ℕ) (γ : ↥Γ), D.zt n ≫ (act (n + 1) γ).hom = (act n γ).hom ≫ D.zt n) ∧

      (∀ (n : ℕ) (γ : ↥Γ), ρ (γ : G) ∈ N → (act n γ).hom = 𝟙 (D.Z n)) ∧

      (∀ (n : ℕ) (γ : ↥Γ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
        (P P' : (Omega K₀ π).obj B), DeligneDatum.IsPullback (K := K₀) (π := π) B (σ (γ : G))⁻¹ P P' →
        D.q n B hB P' = D.q n B hB P ≫ (act n γ).hom) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_monoidHom_aut_forall_q_eq_q_comp_of_le.solution
