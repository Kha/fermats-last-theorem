import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_correspondence_single_of_forall_restrictAlong_eq

open AlgebraicCurve AlgebraicCurve.SemilinearAut
theorem AlgebraicCurve.Divisor.correspondence_single_of_forall_restrictAlong_eq {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (v : Place K F) (hcoll : ∀ w ∈ Place.fiberAlong φ hφ v, w.restrictAlong ψ hψ = v) (n : ℤ) : Divisor.correspondence φ ψ hφ hψ (Finsupp.single v n) = Finsupp.single v (n * ∑ w ∈ Place.fiberAlong φ hφ v, (w.ramificationIndexAlong φ : ℤ) * (w.inertiaDegAlong ψ hψ : ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_correspondence_single_of_forall_restrictAlong_eq.solution
