import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_gradedMonoid_cls_cup_unit

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct DirectSum

universe u
theorem AlgebraicGeometry.OModulePresheaf.exists_gradedMonoid_cls_cup_unit
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R)) (𝒦 : X.OrderedAffineCover) :
    ∃ (H : Type u) (_ : Ring H) (_ : Algebra R H) (𝒜 : ℕ → Submodule R H) (_ : SetLike.GradedMonoid 𝒜)
      (cls : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit π).d 𝒦 n)) →ₗ[R] H),
      (∀ n : ℕ, LinearMap.range (cls n) = 𝒜 n) ∧
      DirectSum.IsInternal 𝒜 ∧
      (∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit π).d 𝒦 0)), cls 0 z = 0 ↔ z = 0) ∧
      (∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit π).d 𝒦 (n + 1)))),
        cls (n + 1) z = 0 ↔ (z : (OModulePresheaf.unit π).cochain 𝒦 (n + 1)) ∈ LinearMap.range ((OModulePresheaf.unit π).d 𝒦 n)) ∧
      (∀ (a b : ℕ) (α : ↥(LinearMap.ker ((OModulePresheaf.unit π).d 𝒦 a))) (β : ↥(LinearMap.ker ((OModulePresheaf.unit π).d 𝒦 b))),
        ∃ hγ : (OModulePresheaf.unit π).cup 𝒦 a b (a + b) rfl α.1 β.1 ∈ LinearMap.ker ((OModulePresheaf.unit π).d 𝒦 (a + b)),
          cls (a + b) ⟨_, hγ⟩ = cls a α * cls b β) ∧
      (∃ h1 : (fun s => (1 : Γ(X, 𝒦.inter s))) ∈ LinearMap.ker ((OModulePresheaf.unit π).d 𝒦 0),
        cls 0 ⟨fun s => (1 : Γ(X, 𝒦.inter s)), h1⟩ = 1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_gradedMonoid_cls_cup_unit.solution
