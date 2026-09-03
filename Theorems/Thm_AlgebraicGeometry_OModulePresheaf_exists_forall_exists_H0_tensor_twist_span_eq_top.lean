import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_exists_H0_tensor_twist_span_eq_top
    {A : Type u} [CommRing A]
    {r : ℕ} {P : Scheme.{u}} (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
    [IsClosedImmersion ι] {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q)
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hq : F.IsQuasicoherent) :
    ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d →
      ∃ (m : ℕ) (σ : Fin m → ↥((F.tensor (ProjSpace.twist q ι d)).H0 (ProjSpace.stdCoverPullback ι))),
        ∀ s : (ProjSpace.stdCoverPullback ι).Idx 0,
          Submodule.span Γ(P, (ProjSpace.stdCoverPullback ι).inter s)
              (Set.range fun l : Fin m =>
                (σ l : (F.tensor (ProjSpace.twist q ι d)).cochain (ProjSpace.stdCoverPullback ι) 0) s) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.solution
