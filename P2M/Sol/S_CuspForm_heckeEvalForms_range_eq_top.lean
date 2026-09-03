import Definitions.Def_CuspForm_HeckeEvalForms
import P2M.Util
namespace P2MW.S_CuspForm_heckeEvalForms_range_eq_top
set_option Elab.async false

set_option autoImplicit false

namespace EVFRangeSol

open CuspForm

variable (N : ℕ) [NeZero N] (k : ℤ)

theorem heckeGenerators_subset :
    heckeGenerators N k ∅ ⊆ (heckeAlgebra N k ∅).val '' Set.range (heckeFormsGen N k) := by
  rintro T (⟨ℓ, hℓ, hℓN, -, rfl⟩ | ⟨q, hqN, hq, -, rfl⟩)
  · refine ⟨heckeFormsGen N k ⟨ℓ, hℓ⟩, ⟨⟨ℓ, hℓ⟩, rfl⟩, ?_⟩
    rw [heckeFormsGen_of_not_dvd (ℓ := ⟨ℓ, hℓ⟩) hℓN]
    rfl
  · refine ⟨heckeFormsGen N k ⟨q, hq⟩, ⟨⟨q, hq⟩, rfl⟩, ?_⟩
    rw [heckeFormsGen_of_dvd (q := ⟨q, hq⟩) hqN]
    rfl

theorem heckeAlgebra_le_map_range :
    heckeAlgebra N k ∅ ≤
      ((MvPolynomial.aeval (R := ℤ) (heckeFormsGen N k)).range).map (heckeAlgebra N k ∅).val := by
  rw [← Algebra.adjoin_range_eq_range_aeval, AlgHom.map_adjoin]
  show Algebra.adjoin ℤ (heckeGenerators N k ∅) ≤ _
  exact Algebra.adjoin_mono (heckeGenerators_subset N k)

theorem heckeEvalForms_surjective : Function.Surjective (heckeEvalForms N k) := by
  intro x
  obtain ⟨y, hy, hyx⟩ := Subalgebra.mem_map.mp (heckeAlgebra_le_map_range N k x.2)
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp hy
  exact ⟨p, Subtype.val_injective hyx⟩

theorem rangeTop : (heckeEvalForms N k).range = ⊤ :=
  RingHom.range_eq_top.mpr (heckeEvalForms_surjective N k)

end EVFRangeSol

theorem solution (N : ℕ) [NeZero N] (k : ℤ) : (CuspForm.heckeEvalForms N k).range = ⊤ :=
  EVFRangeSol.rangeTop N k

#print axioms solution
