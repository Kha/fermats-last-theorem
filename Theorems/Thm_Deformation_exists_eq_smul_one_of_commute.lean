import Mathlib
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_Representation_AbsolutelyIrreducible
import P2M.Util
import P2M.Sol.S_Deformation_exists_eq_smul_one_of_commute

open CategoryTheory IsLocalRing

universe u v
theorem Deformation.exists_eq_smul_one_of_commute {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G]
    {k : Type u} [Field k] {A : Type v} [CommRing A] [IsLocalRing A] (π : A →+* k) (hπ : Function.Surjective π)
    (ρ' : G →* GL n A) (ρ₀ : G →* GL n k)
    [Representation.IsAbsolutelyIrreducible.{u} (Deformation.matrixRepresentation ρ₀)]
    (hlift : ∀ g, ((ρ' g : GL n A) : Matrix n n A).map π = ((ρ₀ g : GL n k) : Matrix n n k))
    (M : Matrix n n A) (hM : ∀ g, ((ρ' g : GL n A) : Matrix n n A) * M = M * ((ρ' g : GL n A) : Matrix n n A)) :
    ∃ a : A, M = a • (1 : Matrix n n A) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_exists_eq_smul_one_of_commute.solution
