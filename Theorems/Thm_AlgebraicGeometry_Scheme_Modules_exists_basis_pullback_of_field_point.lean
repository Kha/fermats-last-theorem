import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_basis_pullback_of_field_point

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
theorem AlgebraicGeometry.Scheme.Modules.exists_basis_pullback_of_field_point
    {X : Scheme.{u}} {M : X.Modules} {n : ℕ} {U : X.Opens} (e : Fin n → Γ(M, U))
    (he : ∀ (W : X.Opens) (hW : W ≤ U), ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W),
      ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i))
    {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ X)
    (hs : s.base (IsLocalRing.closedPoint K) ∈ U) :
    ∃ b : Module.Basis (Fin n) Γ(Spec (CommRingCat.of K), s ⁻¹ᵁ U)
        Γ((Scheme.Modules.pullback s).obj M, s ⁻¹ᵁ U),
      ∀ i, b i = ((Scheme.Modules.pullbackPushforwardAdjunction s).unit.app M).app U (e i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_basis_pullback_of_field_point.solution
