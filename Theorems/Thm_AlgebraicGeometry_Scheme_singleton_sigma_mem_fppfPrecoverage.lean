import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_singleton_sigma_mem_fppfPrecoverage

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.singleton_sigma_mem_fppfPrecoverage
    {R : CommRingCat.{u}} {ι : Type u} [Finite ι] (A : ι → CommRingCat.{u}) (φ : ∀ i, R ⟶ A i)
    (h : Presieve.ofArrows (fun i => Spec (A i)) (fun i => Spec.map (φ i)) ∈ Scheme.fppfPrecoverage (Spec R)) :
    Presieve.singleton (Spec.map (CommRingCat.ofHom (RingHom.pi fun i => (φ i).hom))) ∈
      Scheme.fppfPrecoverage (Spec R) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_singleton_sigma_mem_fppfPrecoverage.solution
