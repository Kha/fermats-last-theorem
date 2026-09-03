import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers
import P2M.Util
namespace P2MW.S_PDivisibleGroup_exists_linearMap_tateModule_apply_eq_of_addMonoidHom_points

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] {L : Type} [Field L] [Algebra R L]
    {h h' : ℕ} (G : PDivisibleGroup R p h) (H : PDivisibleGroup R p h') (F : G.Points L →+ H.Points L) :
    ∃ TF : TateModule p (G.Points L) →ₗ[ℤ_[p]] TateModule p (H.Points L),
      ∀ (x : TateModule p (G.Points L)) (n : ℕ),
        ((TF x : TateModule p (H.Points L)) : ℕ → H.Points L) n = F ((x : ℕ → G.Points L) n) := by
  refine ⟨
    { toFun := fun x => ⟨fun n => F ((x : ℕ → G.Points L) n), fun n =>
        ⟨by rw [← map_zsmul, TateModule.torsion, map_zero], by rw [← map_zsmul, TateModule.compat]⟩⟩,
      map_add' := fun x y => Subtype.ext (funext fun n => by
        show F (((x + y : TateModule p (G.Points L)) : ℕ → G.Points L) n) = _
        rw [TateModule.coe_add, Pi.add_apply, map_add]
        rfl),
      map_smul' := fun a x => Subtype.ext (funext fun n => by
        show F (((a • x : TateModule p (G.Points L)) : ℕ → G.Points L) n) =
          (((a • ⟨fun n => F ((x : ℕ → G.Points L) n), _⟩ : TateModule p (H.Points L))) : ℕ → H.Points L) n
        rw [TateModule.smul_apply, TateModule.smul_apply, map_zsmul]) },
    fun x n => rfl⟩
