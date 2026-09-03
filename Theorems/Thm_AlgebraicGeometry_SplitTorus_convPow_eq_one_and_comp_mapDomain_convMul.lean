import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SplitTorus_convPow_eq_one_and_comp_mapDomain_convMul

set_option autoImplicit false

universe u v

open AlgebraicGeometry AlgebraicGeometry.SplitTorus

theorem AlgebraicGeometry.SplitTorus.convPow_eq_one_and_comp_mapDomain_convMul
    (S : Type u) [CommRing S] (T : Type u) [CommRing T] [Algebra S T] (t m : ℕ) :
    (∀ χ : WithConv (muCoord S t m →ₐ[S] T), χ ^ m = 1) ∧
    (∀ χ χ' : WithConv (muCoord S t m →ₐ[S] T),
      WithConv.toConv ((χ * χ').ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S
          (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)))) =
        WithConv.toConv (χ.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S
          (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)))) * WithConv.toConv (χ'.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S
          (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i))))) ∧
    (WithConv.toConv ((1 : WithConv (muCoord S t m →ₐ[S] T)).ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S
          (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)))) =
      (1 : WithConv (torusCoord S t →ₐ[S] T))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SplitTorus_convPow_eq_one_and_comp_mapDomain_convMul.solution
