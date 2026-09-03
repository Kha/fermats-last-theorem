import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_isOpen_setOf_surjective_baseChange_residueField

universe u v w

open TensorProduct

theorem LinearMap.isOpen_setOf_surjective_baseChange_residueField
    {A : Type u} [CommRing A] {P : Type v} {Q : Type w} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (d : P →ₗ[A] Q) [Module.Finite A (Q ⧸ LinearMap.range d)] :
    IsOpen {𝔭 : PrimeSpectrum A | Function.Surjective (d.baseChange 𝔭.asIdeal.ResidueField)} := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_isOpen_setOf_surjective_baseChange_residueField.solution
