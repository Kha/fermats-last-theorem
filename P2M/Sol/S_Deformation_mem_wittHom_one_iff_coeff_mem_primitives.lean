import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_Dieudonne_WittVectorHom
import P2M.Util
namespace P2MW.S_Deformation_mem_wittHom_one_iff_coeff_mem_primitives

set_option autoImplicit false

p2m_open "Function Deformation P2MW.S_Deformation_mem_wittHom_one_iff_coeff_mem_primitives.Deformation Deformation.TruncWitt"
open scoped TensorProduct

universe u v

namespace Deformation
p2m_export "Deformation" "wittHom mem_wittHom_iff"
namespace WittHomLevelOne
p2m_open "Deformation"

variable {p : ℕ} [Fact p.Prime]

theorem coeff_zero_add {S : Type v} [CommRing S] (a b : TruncatedWittVector p 1 S) :
    (a + b).coeff 0 = a.coeff 0 + b.coeff 0 := by
  obtain ⟨a, rfl⟩ := WittVector.truncate_surjective p 1 S a
  obtain ⟨b, rfl⟩ := WittVector.truncate_surjective p 1 S b
  rw [← map_add, WittVector.coeff_truncate, WittVector.coeff_truncate, WittVector.coeff_truncate]
  exact WittVector.add_coeff_zero a b

omit [Fact p.Prime] in
theorem eq_iff_coeff_zero {S : Type v} [CommRing S] (a b : TruncatedWittVector p 1 S) :
    a = b ↔ a.coeff 0 = b.coeff 0 := by
  refine ⟨fun h => h ▸ rfl, fun h => TruncatedWittVector.ext fun i => ?_⟩
  have hi : i = 0 := Fin.eq_zero i
  subst hi
  exact h

theorem main (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [HopfAlgebra k A] (x : TruncatedWittVector p 1 A) :
    x ∈ wittHom k p 1 A ↔ x.coeff 0 ∈ primitives k A := by
  rw [mem_wittHom_iff, eq_iff_coeff_zero, coeff_zero_add, coeff_map, coeff_map, coeff_map,
    primitives, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sub_apply, sub_sub,
    sub_eq_zero]
  change Coalgebra.comul (R := k) (x.coeff 0) = x.coeff 0 ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] x.coeff 0 ↔
    Coalgebra.comul (R := k) (x.coeff 0) = x.coeff 0 ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] x.coeff 0
  exact Iff.rfl

end Deformation.WittHomLevelOne

theorem solution
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [HopfAlgebra k A] (x : TruncatedWittVector p 1 A) :
    x ∈ Deformation.wittHom k p 1 A ↔ x.coeff 0 ∈ primitives k A :=
  Deformation.WittHomLevelOne.main k p A x
