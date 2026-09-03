import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

theorem AlgebraicGeometry.Scheme.exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois
    (S : Scheme.{0})
    (A : Type) [CommRing A] [HopfAlgebra ℤ A] [Algebra.FiniteType ℤ A]
    (B : Type) [CommRing B] [HopfAlgebra ℤ B] (qc : A →ₐc[ℤ] B)
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K]
    (j : K →ₐc[ℤ] A) (hinj : Function.Injective j)
    (hrange : (j : K →ₐ[ℤ] A).range = HopfAlgebra.hopfKer qc)
    (hHG : HopfAlgebra.IsHopfGalois qc)
    (hff : Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) A)
    (F₀ F₁ L : Sheaf (smallFppfTopology S) Ab.{1})
    (incl : F₀ ⟶ F₁) (pr : F₁ ⟶ L) (hzero : incl ≫ pr = 0)
    (hses : (ShortComplex.mk incl pr hzero).ShortExact)
    (e₁ : ∀ U : S.Fppf, F₁.1.obj (op U) ≃+ Additive (WithConv (A →ₐ[ℤ] Γ(U.left, ⊤))))
    (he₁ : ∀ {U V : S.Fppf} (f : U ⟶ V) (s : F₁.1.obj (op V)) (a : A),
      (Additive.toMul (e₁ U (F₁.1.map f.op s))) a
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e₁ V s)) a))
    (e₀ : ∀ U : S.Fppf, F₀.1.obj (op U) ≃+ Additive (WithConv (B →ₐ[ℤ] Γ(U.left, ⊤))))
    (hincl : ∀ (U : S.Fppf) (s : F₀.1.obj (op U)) (a : A),
      (Additive.toMul (e₁ U (incl.1.app (op U) s))) a = (Additive.toMul (e₀ U s)) (qc a)) :
    ∃ e : ∀ U : S.Fppf, L.1.obj (op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))),
      (∀ (U : S.Fppf) (s : F₁.1.obj (op U)) (k : K),
        (Additive.toMul (e U (pr.1.app (op U) s))) k = (Additive.toMul (e₁ U s)) (j k)) ∧
      ∀ {U V : S.Fppf} (f : U ⟶ V) (s : L.1.obj (op V)) (k : K),
        (Additive.toMul (e U (L.1.map f.op s))) k
          = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois.solution
