import Mathlib
import P2M.Util
namespace P2MW.S_Module_isClosed_setOf_range_le_smul_top

set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R] {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q] (f : P →ₗ[R] Q) :
    IsClosed {x : PrimeSpectrum R | LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule R Q)} := by
  classical
  let s : Set R := {r | ∃ (φ : Q →ₗ[R] R) (p : P), r = φ (f p)}
  suffices h : {x : PrimeSpectrum R | LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule R Q)} = PrimeSpectrum.zeroLocus s by
    rw [h]; exact PrimeSpectrum.isClosed_zeroLocus s
  obtain ⟨sec, hsec⟩ := (inferInstance : Module.Projective R Q).out
  ext x
  simp only [Set.mem_setOf_eq, PrimeSpectrum.mem_zeroLocus]
  constructor
  · intro hx
    rintro r ⟨φ, p, rfl⟩
    have hfp : f p ∈ x.asIdeal • (⊤ : Submodule R Q) := hx ⟨p, rfl⟩
    show φ (f p) ∈ x.asIdeal
    refine Submodule.smul_induction_on (p := fun q => φ q ∈ x.asIdeal) hfp ?_ ?_
    · intro a ha q _
      rw [map_smul, smul_eq_mul]; exact Ideal.mul_mem_right _ _ ha
    · intro u v hu hv
      rw [map_add]; exact Ideal.add_mem _ hu hv
  · intro hx
    rintro _ ⟨p, rfl⟩
    rw [← hsec (f p), Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun q _ => ?_
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    exact hx ⟨(Finsupp.lapply q).comp sec, p, rfl⟩
