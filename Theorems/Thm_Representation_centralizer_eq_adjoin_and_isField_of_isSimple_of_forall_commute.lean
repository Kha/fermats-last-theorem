import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.Adjoin.Basic
import P2M.Util
import P2M.Sol.S_Representation_centralizer_eq_adjoin_and_isField_of_isSimple_of_forall_commute

theorem Representation.centralizer_eq_adjoin_and_isField_of_isSimple_of_forall_commute
    {k : Type*} [Field k] {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module k V]
    [Nontrivial V] (ρ : Representation k Γ V)
    (hsimple : ∀ W : Submodule k V, (∀ (g : Γ) (v : V), v ∈ W → ρ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hcomm : ∀ a b : Γ, ρ a * ρ b = ρ b * ρ a) :
    Subalgebra.centralizer k (Set.range (ρ : Γ → Module.End k V))
        = Algebra.adjoin k (Set.range (ρ : Γ → Module.End k V)) ∧
    IsField (Subalgebra.centralizer k (Set.range (ρ : Γ → Module.End k V))) ∧
    ∀ v : V, v ≠ 0 → Function.Bijective
      (fun φ : Subalgebra.centralizer k (Set.range (ρ : Γ → Module.End k V)) =>
        (φ : Module.End k V) v) := by p2m_exact_reverting @_root_.P2MW.S_Representation_centralizer_eq_adjoin_and_isField_of_isSimple_of_forall_commute.solution
