import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RiemannForm_exists_addSubgroup_mem_iff_nonempty_pullback_translation_iso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.exists_addSubgroup_mem_iff_nonempty_pullback_translation_iso
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (𝓛 : A.Modules) :
    ∃ H : AddSubgroup (L.AlgPoints hc k), ∀ Q : L.AlgPoints hc k,
      Q ∈ H ↔ Nonempty ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛 ≅ 𝓛) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RiemannForm_exists_addSubgroup_mem_iff_nonempty_pullback_translation_iso.solution
