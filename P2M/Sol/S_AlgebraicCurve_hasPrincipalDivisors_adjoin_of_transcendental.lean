module

import P2M.Sol.S_AlgebraicCurve_hasPrincipalDivisors_of_transcendental
import P2M.Util
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup

namespace P2MW.S_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental

noncomputable section
open IntermediateField

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "HasPrincipalDivisors hasPrincipalDivisors_of_transcendental"
p2m_open "AlgebraicCurve"
namespace W2

variable (K : Type*) [Field K] [CharZero K] {LF : Type*} [Field LF] [Algebra K LF]

theorem hasPrincipalDivisors_adjoin (x : LF) (hx : Transcendental K x) (T : Finset LF)
    (hT : ∀ t ∈ T, IsIntegral (IntermediateField.adjoin K ({x} : Set LF)) t) :
    HasPrincipalDivisors K (IntermediateField.adjoin K (insert x (T : Set LF))) := by
  set F : IntermediateField K LF := IntermediateField.adjoin K (insert x (T : Set LF)) with hF
  have hxF : x ∈ F := subset_adjoin K _ (Set.mem_insert x _)
  have hTF : ∀ t ∈ T, t ∈ F := fun t ht => subset_adjoin K _ (Set.mem_insert_of_mem x ht)
  set x' : F := ⟨x, hxF⟩ with hx'

  have hx't : Transcendental K x' :=
    (transcendental_algebraMap_iff (R := K) (S := F) (A := LF) Subtype.val_injective).mp hx

  set A : IntermediateField K F := IntermediateField.adjoin K ({x'} : Set F) with hA
  have hliftA : lift A = IntermediateField.adjoin K ({x} : Set LF) := by
    rw [hA, lift_adjoin_simple]

  let e : A ≃ₐ[K] IntermediateField.adjoin K ({x} : Set LF) :=
    (liftAlgEquiv A).trans (equivOfEq hliftA)
  have he : ∀ a : A, ((e a : IntermediateField.adjoin K ({x} : Set LF)) : LF) = ((a : F) : LF) := by
    intro a; rfl

  have hint : ∀ t (ht : t ∈ T), IsIntegral A (⟨t, hTF t ht⟩ : F) := by
    intro t ht

    have h1 : IsIntegral A (t : LF) := by
      refine (hT t ht).map_of_comp_eq (R := IntermediateField.adjoin K ({x} : Set LF)) (S := LF) (T := A) (U := LF)
        (e.symm : IntermediateField.adjoin K ({x} : Set LF) →+* A) (RingHom.id LF) ?_
      ext b
      change (((e.symm b : A) : F) : LF) = ((b : IntermediateField.adjoin K ({x} : Set LF)) : LF)
      rw [← he (e.symm b), AlgEquiv.apply_symm_apply]
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A F LF) Subtype.val_injective).mp h1

  haveI : FiniteDimensional A F := by
    set T' : Set F := (fun t : T => (⟨(t : LF), hTF t t.2⟩ : F)) '' Set.univ with hT'
    haveI : Finite T' := Set.Finite.to_subtype ((Set.finite_univ).image _)
    have hT'int : ∀ y ∈ T', IsIntegral A y := by
      rintro _ ⟨t, -, rfl⟩; exact hint t t.2
    haveI : FiniteDimensional A (IntermediateField.adjoin A T') := finiteDimensional_adjoin hT'int

    have htop : IntermediateField.adjoin A T' = ⊤ := by
      apply restrictScalars_injective K
      rw [restrictScalars_adjoin, restrictScalars_top]
      apply lift_injective
      rw [lift_top, lift_adjoin]
      apply le_antisymm (adjoin_le_iff.mpr ?_) ?_
      · rintro _ ⟨y, hy, rfl⟩; exact y.2
      · show IntermediateField.adjoin K (insert x (T : Set LF)) ≤ _
        apply adjoin.mono
        intro z hz
        rcases hz with rfl | hz
        · exact ⟨x', Or.inl (subset_adjoin K _ (Set.mem_singleton _)), rfl⟩
        · exact ⟨⟨z, hTF z hz⟩, Or.inr ⟨⟨z, hz⟩, Set.mem_univ _, rfl⟩, rfl⟩
    rw [htop] at this
    exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := A) (E := F)).toLinearEquiv
  exact hasPrincipalDivisors_of_transcendental K x' hx't

end W2
end AlgebraicCurve

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental.AlgebraicCurve"

theorem solution (K : Type*) [Field K] [CharZero K] {LF : Type*} [Field LF] [Algebra K LF]
    (x : LF) (hx : Transcendental K x) (T : Finset LF)
    (hT : ∀ t ∈ T, IsIntegral (IntermediateField.adjoin K ({x} : Set LF)) t) :
    HasPrincipalDivisors K (IntermediateField.adjoin K (insert x (T : Set LF))) :=
  AlgebraicCurve.W2.hasPrincipalDivisors_adjoin K x hx T hT

end
end S_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental
end P2MW

public section
open AlgebraicCurve
theorem AlgebraicCurve.hasPrincipalDivisors_adjoin_of_transcendental (K : Type*) [Field K] [CharZero K] {LF : Type*} [Field LF] [Algebra K LF]
    (x : LF) (hx : Transcendental K x) (T : Finset LF)
    (hT : ∀ t ∈ T, IsIntegral (IntermediateField.adjoin K ({x} : Set LF)) t) :
    HasPrincipalDivisors K (IntermediateField.adjoin K (insert x (T : Set LF))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental.solution
end
