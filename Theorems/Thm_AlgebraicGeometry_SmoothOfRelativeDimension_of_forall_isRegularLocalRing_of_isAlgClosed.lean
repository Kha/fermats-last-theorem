import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmoothOfRelativeDimension_of_forall_isRegularLocalRing_of_isAlgClosed

universe u

theorem AlgebraicGeometry.SmoothOfRelativeDimension.of_forall_isRegularLocalRing_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k]
    (R : Type u) [CommRing R] [Algebra k R] [Algebra.FiniteType k R] (n : ℕ)
    (hreg : ∀ (p : Ideal R) (_ : p.IsMaximal),
      IsRegularLocalRing (Localization.AtPrime p) ∧
        ringKrullDim (Localization.AtPrime p) = (n : ℕ∞)) :
    SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (algebraMap k R)) : Spec _ ⟶ Spec (CommRingCat.of k)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_of_forall_isRegularLocalRing_of_isAlgClosed.solution
