import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import P2M.Util
import P2M.Sol.S_Module_projective_of_isReduced_of_finrank_fiber_const

universe u v

open scoped TensorProduct

theorem Module.projective_of_isReduced_of_finrank_fiber_const {R : Type u} [CommRing R]
    [IsReduced R] {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    {e : ℕ} (h : ∀ 𝔭 : PrimeSpectrum R,
      Module.finrank 𝔭.asIdeal.ResidueField (𝔭.asIdeal.ResidueField ⊗[R] M) = e) :
    Module.Projective R M := by p2m_exact_reverting @_root_.P2MW.S_Module_projective_of_isReduced_of_finrank_fiber_const.solution
