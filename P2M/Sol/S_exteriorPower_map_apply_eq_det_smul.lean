import Mathlib
import Theorems.Thm_exteriorPower_iotaMulti_comp_eq_det_smul
import P2M.Util
namespace P2MW.S_exteriorPower_map_apply_eq_det_smul

set_option autoImplicit false

theorem solution {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] {ι : Type*} [Fintype ι] (b : Module.Basis ι A M) {n : ℕ} (hn : Fintype.card ι = n)
    (f : M →ₗ[A] M) (x : ⋀[A]^n M) :
    exteriorPower.map n f x = LinearMap.det f • x := by
  classical
  let b' : Module.Basis (Fin n) A M := b.reindex (Fintype.equivFinOfCardEq hn)
  have hgen : ∀ m : Fin n → M,
      exteriorPower.map n f (exteriorPower.ιMulti A n m) = LinearMap.det f • exteriorPower.ιMulti A n m := by
    intro m
    rw [exteriorPower.map_apply_ιMulti]
    exact exteriorPower.iotaMulti_comp_eq_det_smul b' f m
  have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨m, rfl⟩ := hy; exact hgen m
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, smul_add]
  | smul r y _ hy => rw [map_smul, hy, smul_comm]
