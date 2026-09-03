import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_ofArrows_mem_fppfPrecoverage_of_mem_fppfTopology

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_ofArrows_mem_fppfPrecoverage_of_mem_fppfTopology
    {R : CommRingCat.{u}} (S : Sieve (Spec R)) (hS : S ∈ Scheme.fppfTopology (Spec R)) :
    ∃ (ι : Type u) (_ : Finite ι) (A : ι → CommRingCat.{u}) (φ : ∀ i, R ⟶ A i),
      Presieve.ofArrows (fun i => Spec (A i)) (fun i => Spec.map (φ i)) ∈ Scheme.fppfPrecoverage (Spec R) ∧
      ∀ i, S (Spec.map (φ i)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_ofArrows_mem_fppfPrecoverage_of_mem_fppfTopology.solution
