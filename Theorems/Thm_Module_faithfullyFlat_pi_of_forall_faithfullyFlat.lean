import Mathlib
import P2M.Util
import P2M.Sol.S_Module_faithfullyFlat_pi_of_forall_faithfullyFlat

set_option autoImplicit false

theorem Module.faithfullyFlat_pi_of_forall_faithfullyFlat
    {k : ℕ} (C : Fin k → Type) [∀ i, CommRing (C i)] (D : Fin k → Type) [∀ i, CommRing (D i)] [∀ i, Algebra (C i) (D i)]
    [inst : Algebra (∀ i, C i) (∀ i, D i)]
    (halg : ∀ (i : Fin k) (x : ∀ i, C i), algebraMap (∀ i, C i) (∀ i, D i) x i = algebraMap (C i) (D i) (x i))
    (hff : ∀ i, Module.FaithfullyFlat (C i) (D i)) :
    @Module.FaithfullyFlat (∀ i, C i) (∀ i, D i) _ _ inst.toModule := by p2m_exact_reverting @_root_.P2MW.S_Module_faithfullyFlat_pi_of_forall_faithfullyFlat.solution
