import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Noetherian.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom

open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.OModulePresheaf.AffSES.exists_connectingHom {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π] {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover) : ∃ (δ₀ : F₃.H0 K →ₗ[R] F₁.HSucc K 0) (δ : ∀ i : ℕ, F₃.HSucc K i →ₗ[R] F₁.HSucc K (i + 1)), LinearMap.ker δ₀ ≤ LinearMap.range (S.proj.H0Map K) ∧ (∀ i, LinearMap.ker (δ i) ≤ LinearMap.range (S.proj.HSuccMap K i)) ∧ LinearMap.ker (S.inc.HSuccMap K 0) ≤ LinearMap.range δ₀ ∧ (∀ i, LinearMap.ker (S.inc.HSuccMap K (i + 1)) ≤ LinearMap.range (δ i)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom.solution
