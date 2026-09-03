import Mathlib
import Definitions.Def_Algebra_PointDerivations
import P2M.Util
namespace P2MW.S_Algebra_PointDerivations_exists_eq_and_map_eq_map_of_forall_apply_eq

set_option autoImplicit false

open TensorProduct

universe u

theorem solution
    {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A] (ev : A →+* k)
    (M M' N : Type u) [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] [AddCommGroup N] [Module k N]
    (c : ↥(Algebra.PointDerivations k A ev M)) (g : M →ₗ[k] N) (σ : M' →ₗ[k] N) (hσ : Function.Injective σ)
    (cs : A → M') (h : ∀ a : A, σ (cs a) = g (c.1 a)) :
    ∃ δ : ↥(Algebra.PointDerivations k A ev M'),
      (∀ a : A, δ.1 a = cs a) ∧ Algebra.PointDerivations.map ev σ δ = Algebra.PointDerivations.map ev g c := by
  classical

  have hadd : ∀ a b, cs (a + b) = cs a + cs b := fun a b => hσ (by rw [map_add, h, h, h, map_add, map_add])
  have hsmul : ∀ (r : k) a, cs (r • a) = r • cs a := fun r a => hσ (by rw [map_smul, h, h, map_smul, map_smul])
  let D : A →ₗ[k] M' := { toFun := cs, map_add' := hadd, map_smul' := hsmul }
  have hD : D ∈ Algebra.PointDerivations k A ev M' := by
    intro a b
    apply hσ
    show σ (cs (a * b)) = σ (ev a • cs b + ev b • cs a)
    rw [map_add, map_smul, map_smul, h, h, h, c.2 a b, map_add, map_smul, map_smul]
  refine ⟨⟨D, hD⟩, fun a => rfl, ?_⟩
  apply Subtype.ext
  ext a
  show σ (cs a) = g (c.1 a)
  exact h a
