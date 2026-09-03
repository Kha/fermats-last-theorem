import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Divisor_correspondence_single

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (v : Place K F) (n : ℤ) : Divisor.correspondence φ ψ hφ hψ (Finsupp.single v n) = ∑ w ∈ Place.fiberAlong φ hφ v, Finsupp.single (w.restrictAlong ψ hψ) (n * (w.ramificationIndexAlong φ : ℤ) * (w.inertiaDegAlong ψ hψ : ℤ)) := by
  rw [Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum]
  exact Finset.sum_congr rfl fun w _ => Divisor.pushforwardAlong_single ψ hψ w _

end
