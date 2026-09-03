import Mathlib
import P2M.Util
import P2M.Sol.S_LinearIndependent_linearMap_baseChange_of_int

open scoped TensorProduct

theorem LinearIndependent.linearMap_baseChange_of_int (K : Type) [Field K] [CharZero K]
    (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ] {ι : Type}
    (f : ι → Module.End ℤ Λ) (hf : LinearIndependent ℤ f) :
    LinearIndependent K (fun i => ((f i).baseChange K : Module.End K (K ⊗[ℤ] Λ))) := by p2m_exact_reverting @_root_.P2MW.S_LinearIndependent_linearMap_baseChange_of_int.solution
