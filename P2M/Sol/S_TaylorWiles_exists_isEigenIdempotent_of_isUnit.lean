import Mathlib
import Definitions.Def_Deformations_LocalSplitting
import Theorems.Thm_TaylorWiles_isEigenIdempotent_smul_sub
import P2M.Util
namespace P2MW.S_TaylorWiles_exists_isEigenIdempotent_of_isUnit

set_option autoImplicit false

universe u v

open Matrix

open TaylorWiles in
theorem solution {A : Type u} [CommRing A] {M : Matrix (Fin 2) (Fin 2) A} {a b : A}
    (htr : M.trace = a + b) (hdet : M.det = a * b) (hu : IsUnit (a - b)) :
    ∃ e, TaylorWiles.IsEigenIdempotent M a b e := by
  obtain ⟨u, hu⟩ := hu
  refine ⟨_, TaylorWiles.isEigenIdempotent_smul_sub htr hdet (v := ((u⁻¹ : Aˣ) : A)) ?_⟩
  rw [← hu]
  exact u.inv_mul
