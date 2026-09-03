import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_finset_forall_exists_subalgebra_isPushout_of_span_eq_top

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.exists_finset_forall_exists_subalgebra_isPushout_of_span_eq_top
    {S T : Type} [CommRing S] [CommRing T] [Algebra S T] [Module.Projective S T]
    {ι : Type} [Finite ι] (g : ι → T) (hg : Submodule.span S (Set.range g) = ⊤) :
    ∃ c : Finset S, ∀ S₀ : Subalgebra ℤ S, ↑c ⊆ (S₀ : Set S) →
      ∃ T₀ : Subalgebra S₀ T, Subalgebra.toSubmodule T₀ = Submodule.span S₀ (Set.range g) ∧
        Module.Finite S₀ T₀ ∧ Module.Projective S₀ T₀ ∧
        (LinearIndependent S g → Module.Free S₀ T₀) ∧ Algebra.IsPushout S₀ S T₀ T := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_finset_forall_exists_subalgebra_isPushout_of_span_eq_top.solution
