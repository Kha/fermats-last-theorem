import Definitions.Def_CerednikDrinfeld_MumfordTower
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_action_forall_q_eq_q_comp

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordTower.exists_action_forall_q_eq_q_comp
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] (r : ℕ)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (N : Subgroup (PGL(2, K₀)))
    (D : MumfordTower 𝒪 π K₀ r g₁ N) :
    ∃ a : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀),
        (∀ x : PGL(2, K₀), x ∈ N ↔ Matrix.ProjGenLinGroup.mk g * x * (Matrix.ProjGenLinGroup.mk g)⁻¹ ∈ N) → ∀ n : ℕ, D.Z n ≅ D.Z n,

      (∀ g hg (n : ℕ), (a g hg n).hom ≫ D.zb n = D.zb n) ∧

      (∀ g hg (n : ℕ), D.zt n ≫ (a g hg (n + 1)).hom = (a g hg n).hom ≫ D.zt n) ∧

      (∀ g hg (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
        (P P' : (Omega K₀ π).obj B), DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' →
        D.q n B hB P' = D.q n B hB P ≫ (a g hg n).hom) ∧

      (∀ g hg (n : ℕ) (b : D.Z n ⟶ D.Z n),
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
          (P P' : (Omega K₀ π).obj B), DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' →
          D.q n B hB P' = D.q n B hB P ≫ b) → b = (a g hg n).hom) ∧

      (∀ g hg (n : ℕ), Matrix.ProjGenLinGroup.mk g ∈ N → (a g hg n).hom = 𝟙 (D.Z n)) ∧

      (∀ g hg g' hg' (hgg' : ∀ x : PGL(2, K₀), x ∈ N ↔
          Matrix.ProjGenLinGroup.mk (g * g') * x * (Matrix.ProjGenLinGroup.mk (g * g'))⁻¹ ∈ N) (n : ℕ),
        (a (g * g') hgg' n).hom = (a g' hg' n).hom ≫ (a g hg n).hom) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_action_forall_q_eq_q_comp.solution
