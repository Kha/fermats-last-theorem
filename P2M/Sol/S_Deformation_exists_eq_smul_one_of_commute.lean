import Mathlib
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_Representation_AbsolutelyIrreducible
import Theorems.Thm_Matrix_exists_eq_smul_one_of_commute_of_map_span_eq_top
import Theorems.Thm_Representation_span_range_eq_top_of_isAbsolutelyIrreducible_matrix
import P2M.Util
namespace P2MW.S_Deformation_exists_eq_smul_one_of_commute

universe u v

theorem solution {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G]
    {k : Type u} [Field k] {A : Type v} [CommRing A] [IsLocalRing A] (π : A →+* k) (hπ : Function.Surjective π)
    (ρ' : G →* GL n A) (ρ₀ : G →* GL n k)
    [Representation.IsAbsolutelyIrreducible.{u} (Deformation.matrixRepresentation ρ₀)]
    (hlift : ∀ g, ((ρ' g : GL n A) : Matrix n n A).map π = ((ρ₀ g : GL n k) : Matrix n n k))
    (M : Matrix n n A) (hM : ∀ g, ((ρ' g : GL n A) : Matrix n n A) * M = M * ((ρ' g : GL n A) : Matrix n n A)) :
    ∃ a : A, M = a • (1 : Matrix n n A) := by
  refine Matrix.exists_eq_smul_one_of_commute_of_map_span_eq_top π hπ
    (S := Set.range fun g => (ρ' g).val) ?_ M ?_
  · rw [show ((fun X : Matrix n n A => X.map π) '' Set.range fun g => (ρ' g).val) =
      Set.range fun g => (ρ₀ g).val by
        rw [← Set.range_comp]; exact congrArg Set.range (funext fun g => hlift g)]
    exact Representation.span_range_eq_top_of_isAbsolutelyIrreducible_matrix ρ₀
  · rintro X ⟨g, rfl⟩
    exact hM g
