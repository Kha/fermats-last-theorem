import Definitions.Def_TaylorWiles_Primes
import P2M.Util
namespace P2MW.S_Matrix_hasDistinctRationalEigenvalues_of_isConj

theorem solution {R : Type*} [CommRing R]
    {M N : Matrix (Fin 2) (Fin 2) R} (h : IsConj M N)
    (hM : M.HasDistinctRationalEigenvalues) : N.HasDistinctRationalEigenvalues := by
  obtain ⟨α, β, hne, h1, h2⟩ := hM
  refine ⟨α, β, hne, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := h
    have key : (c : Matrix (Fin 2) (Fin 2) R) * M * (↑c⁻¹ : Matrix (Fin 2) (Fin 2) R) = N := by
      rw [hc.eq, mul_assoc, Units.mul_inv, mul_one]
    rw [← key, Matrix.trace_units_conj, h1]
  · have hdet : N.det = M.det := by
      have := isConj_iff_eq.mp ((Matrix.detMonoidHom (n := Fin 2) (R := R)).map_isConj h.symm)
      simpa [Matrix.coe_detMonoidHom] using this
    rw [hdet, h2]
