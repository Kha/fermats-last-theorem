import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_algHom_cls_eq_cls_unitPullback
attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableOSub

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct DirectSum

universe u
theorem AlgebraicGeometry.OModulePresheaf.exists_algHom_cls_eq_cls_unitPullback
    {R : Type u} [CommRing R] {X Y : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (hh : h ≫ πY = πX)
    (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w))
    (H : Type u) [Ring H] [Algebra R H] (𝒜 : ℕ → Submodule R H) [SetLike.GradedMonoid 𝒜]
    (cls : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 n)) →ₗ[R] H)
    (cls_range : ∀ n : ℕ, LinearMap.range (cls n) = 𝒜 n)
    (cls_zero : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 0)), cls 0 z = 0 ↔ z = 0)
    (cls_succ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 (n + 1)))),
      cls (n + 1) z = 0 ↔ (z : (OModulePresheaf.unit πY).cochain 𝒦 (n + 1)) ∈ LinearMap.range ((OModulePresheaf.unit πY).d 𝒦 n))
    (cls_mul : ∀ (a b : ℕ) (α : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 a))) (β : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 b))),
      ∃ hγ : (OModulePresheaf.unit πY).cup 𝒦 a b (a + b) rfl α.1 β.1 ∈ LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 (a + b)),
        cls (a + b) ⟨_, hγ⟩ = cls a α * cls b β)
    (cls_internal : DirectSum.IsInternal 𝒜)
    (cls_one : ∃ h1 : (fun s => (1 : Γ(Y, 𝒦.inter s))) ∈ LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 0),
      cls 0 ⟨fun s => (1 : Γ(Y, 𝒦.inter s)), h1⟩ = 1)
    (H' : Type u) [Ring H'] [Algebra R H'] (𝒜' : ℕ → Submodule R H') [SetLike.GradedMonoid 𝒜']
    (cls' : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 n)) →ₗ[R] H')
    (cls'_range : ∀ n : ℕ, LinearMap.range (cls' n) = 𝒜' n)
    (cls'_zero : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 0)), cls' 0 z = 0 ↔ z = 0)
    (cls'_succ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 (n + 1)))),
      cls' (n + 1) z = 0 ↔ (z : (OModulePresheaf.unit πX).cochain 𝒲 (n + 1)) ∈ LinearMap.range ((OModulePresheaf.unit πX).d 𝒲 n))
    (cls'_mul : ∀ (a b : ℕ) (α : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 a))) (β : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 b))),
      ∃ hγ : (OModulePresheaf.unit πX).cup 𝒲 a b (a + b) rfl α.1 β.1 ∈ LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 (a + b)),
        cls' (a + b) ⟨_, hγ⟩ = cls' a α * cls' b β)
    (cls'_one : ∃ h1 : (fun s => (1 : Γ(X, 𝒲.inter s))) ∈ LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 0),
      cls' 0 ⟨fun s => (1 : Γ(X, 𝒲.inter s)), h1⟩ = 1)
    :
    ∃ p : H →ₐ[R] H',
      (∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 n))),
        ∃ hz : OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z.1 ∈ LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 n),
          p (cls n z) = cls' n ⟨_, hz⟩) ∧
      (∀ n : ℕ, (𝒜 n).map p.toLinearMap ≤ 𝒜' n) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_algHom_cls_eq_cls_unitPullback.solution
