import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import P2M.Util
import P2M.Sol.S_DoubleComplex_boundedSpectralSequence

set_option autoImplicit false

universe u

theorem DoubleComplex.boundedSpectralSequence : DoubleComplex.BoundedSpectralSequence.{u} := by p2m_exact_reverting @_root_.P2MW.S_DoubleComplex_boundedSpectralSequence.solution
