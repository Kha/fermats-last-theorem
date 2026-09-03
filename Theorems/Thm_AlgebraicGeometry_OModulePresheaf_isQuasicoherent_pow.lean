import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow

open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.OModulePresheaf.isQuasicoherent_pow {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F : OModulePresheaf π} (n : ℕ) (hF : F.IsQuasicoherent) : (F.pow n).IsQuasicoherent := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow.solution
