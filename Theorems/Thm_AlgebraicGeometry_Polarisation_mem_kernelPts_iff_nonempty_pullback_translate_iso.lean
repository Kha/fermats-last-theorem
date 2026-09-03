import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_translate_iso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.mem_kernelPts_iff_nonempty_pullback_translate_iso
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (𝓛 : A.Modules) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    x ∈ kernelPts f L 𝓛 ↔ Nonempty ((Scheme.Modules.pullback (L.translate x)).obj 𝓛 ≅ 𝓛) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_translate_iso.solution
