import Definitions.Def_AutomorphicForm_UnipotentQuotient
import P2M.Util
namespace P2MW.S_AutomorphicForm_isClosed_adelicUnipotent

set_option autoImplicit false

open NumberField AutomorphicForm

noncomputable section

namespace AdelicUnipotentClosed

variable (K : Type) [Field K] [NumberField K]

private theorem coe_adelicUnipotent_eq :
    ((adelicUnipotent K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)) =
      {g : AdelicGL2 (𝓞 K) K | (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 = 1 ∧
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 = 1} := by
  ext g
  constructor
  · rintro ⟨y, rfl⟩
    change ((unipotentGL2 y.toAdd : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 = 1 ∧
      ((unipotentGL2 y.toAdd : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
      ((unipotentGL2 y.toAdd : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 = 1
    simp [unipotentGL2_coe]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1), ?_⟩
    change (unipotentGL2 ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1) :
      AdelicGL2 (𝓞 K) K) = g
    refine Units.ext ?_
    rw [unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

private theorem isClosed_adelicUnipotent :
    IsClosed ((adelicUnipotent K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)) := by
  rw [coe_adelicUnipotent_eq]
  have hc : Continuous fun g : AdelicGL2 (𝓞 K) K =>
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := Units.continuous_val
  refine (isClosed_eq (hc.matrix_elem 0 0) continuous_const).inter
    ((isClosed_eq (hc.matrix_elem 1 0) continuous_const).inter
      (isClosed_eq (hc.matrix_elem 1 1) continuous_const))

end AdelicUnipotentClosed

theorem solution (K : Type) [Field K] [NumberField K] :
    IsClosed ((adelicUnipotent K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)) :=
  AdelicUnipotentClosed.isClosed_adelicUnipotent K

end
