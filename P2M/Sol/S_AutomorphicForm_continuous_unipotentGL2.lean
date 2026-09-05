import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
namespace P2MW.S_AutomorphicForm_continuous_unipotentGL2

open AutomorphicForm

namespace M4aP3B
namespace CTU

variable {R : Type*} [CommRing R]

theorem unipotentGL2_inv (x : R) : (unipotentGL2 x)⁻¹ = unipotentGL2 (-x) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

end M4aP3B.CTU

theorem solution {R : Type*} [CommRing R] [TopologicalSpace R]
    [ContinuousNeg R] : Continuous fun x : R => AutomorphicForm.unipotentGL2 x := by
  have hval : Continuous fun x : R =>
      ((AutomorphicForm.unipotentGL2 x : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
    refine continuous_matrix fun i j => ?_
    simp only [AutomorphicForm.unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  simp only [M4aP3B.CTU.unipotentGL2_inv]
  exact hval.comp continuous_neg

