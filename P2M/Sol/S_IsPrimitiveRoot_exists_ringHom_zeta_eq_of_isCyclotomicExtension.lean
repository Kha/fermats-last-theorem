import Mathlib
import P2M.Util
namespace P2MW.S_IsPrimitiveRoot_exists_ringHom_zeta_eq_of_isCyclotomicExtension

set_option autoImplicit false

open IsLocalRing Polynomial

theorem solution
    (n : ℕ) [NeZero n] (K : Type*) [Field K] [Algebra ℚ K] [IsCyclotomicExtension {n} ℚ K]
    (L : Type*) [Field L] [CharZero L] (ξ : L) (hξ : IsPrimitiveRoot ξ n) :
    ∃ φ : K →+* L, φ (IsCyclotomicExtension.zeta n ℚ K) = ξ := by
  classical
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ K
  have hirr : Irreducible (cyclotomic n ℚ) := cyclotomic.irreducible_rat (NeZero.pos n)
  let E := hζ.embeddingsEquivPrimitiveRoots L hirr
  have hξmem : ξ ∈ primitiveRoots n L := (mem_primitiveRoots (NeZero.pos n)).mpr hξ
  let φ : K →ₐ[ℚ] L := E.symm ⟨ξ, hξmem⟩
  refine ⟨φ.toRingHom, ?_⟩
  have : (E φ : L) = φ (IsCyclotomicExtension.zeta n ℚ K) := hζ.embeddingsEquivPrimitiveRoots_apply_coe L hirr φ
  rw [show E φ = ⟨ξ, hξmem⟩ from E.apply_symm_apply _] at this
  exact this.symm
