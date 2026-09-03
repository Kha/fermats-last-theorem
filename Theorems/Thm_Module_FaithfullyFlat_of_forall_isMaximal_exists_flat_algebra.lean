import Mathlib
import P2M.Util
import P2M.Sol.S_Module_FaithfullyFlat_of_forall_isMaximal_exists_flat_algebra

universe u v

theorem Module.FaithfullyFlat.of_forall_isMaximal_exists_flat_algebra
    (B : Type u) [CommRing B] (H : Type v) [AddCommGroup H] [Module B H]
    (h : ∀ (M : Ideal B), M.IsMaximal →
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C) (_ : Module.Flat B C),
        M.map (algebraMap B C) ≠ ⊤ ∧ Module.FaithfullyFlat C (TensorProduct B C H)) :
    Module.FaithfullyFlat B H := by p2m_exact_reverting @_root_.P2MW.S_Module_FaithfullyFlat_of_forall_isMaximal_exists_flat_algebra.solution
