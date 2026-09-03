import Mathlib
import P2M.Util
import P2M.Sol.S_DualAssembly_injective_gram_of_forall_joint_eigenvector_mul

set_option autoImplicit false

open scoped TensorProduct

theorem DualAssembly.injective_gram_of_forall_joint_eigenvector_mul (p : ℕ) [Fact p.Prime]
    {T : Type*} [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T]
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra ℤ_[p] K] (hK : Function.Injective (algebraMap ℤ_[p] K))
    (c : ℤ_[p]) (hc : c ≠ 0) (A B : Module.End ℤ_[p] T) (hAB : Commute A B)
    (h : ∀ (v : K ⊗[ℤ_[p]] T) (a b : K), v ≠ 0 → A.baseChange K v = a • v → B.baseChange K v = b • v →
      a * b ≠ (algebraMap ℤ_[p] K c) ^ 2) :
    Function.Injective (fun z : T × T => (c • z.1 + A z.2, B z.1 + c • z.2)) := by p2m_exact_reverting @_root_.P2MW.S_DualAssembly_injective_gram_of_forall_joint_eigenvector_mul.solution
