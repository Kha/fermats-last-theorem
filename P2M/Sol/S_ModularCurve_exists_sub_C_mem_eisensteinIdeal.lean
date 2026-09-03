import Definitions.Def_HeckeGalois_EichlerShimura
import P2M.Util
namespace P2MW.S_ModularCurve_exists_sub_C_mem_eisensteinIdeal

set_option autoImplicit false

open ModularCurve

namespace S09A1C

open ModularCurve

theorem exists_sub_C_mem_eisensteinIdeal (N : ℕ) (t : HeckeAlg) :
    ∃ n : ℤ, t - MvPolynomial.C n ∈ eisensteinIdeal N := by
  refine ⟨MvPolynomial.aeval (eisensteinSystem N) t, ?_⟩
  rw [eisensteinIdeal, mem_eigenIdeal_iff, map_sub, MvPolynomial.aeval_C]
  simp

theorem surjective_algebraMap_quotient_eisensteinIdeal (N : ℕ) :
    Function.Surjective (algebraMap ℤ (HeckeAlg ⧸ eisensteinIdeal N)) := by
  intro x
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨n, hn⟩ := exists_sub_C_mem_eisensteinIdeal N t
  refine ⟨n, ?_⟩
  rw [IsScalarTower.algebraMap_apply ℤ HeckeAlg (HeckeAlg ⧸ eisensteinIdeal N), MvPolynomial.algebraMap_eq,
    Ideal.Quotient.algebraMap_eq]
  exact (Ideal.Quotient.eq.mpr hn).symm

end S09A1C

theorem solution (N : ℕ) (t : HeckeAlg) : ∃ n : ℤ, t - MvPolynomial.C n ∈ eisensteinIdeal N := by
  exact S09A1C.exists_sub_C_mem_eisensteinIdeal N t
