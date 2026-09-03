import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_CharacterLatticePairings
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_toricPts_characterLattice_hom_of_ptsSp_nodeUnit

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP
  ModularCurve.CharacterLattice

theorem ModularCurve.JHNeronObjectAtP.exists_addEquiv_toricPts_characterLattice_hom_of_ptsSp_nodeUnit
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (m : ℕ) (hm : 0 < m) (hmp : m.Coprime p)
    (hker : ∀ wb : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ,
      GluedPic0.nodeUnit O.ssFinset wb = 0 → ∃ c : (ResidueField ↥A)ˣ, wb = fun _ => Additive.ofMul c) :
    ∃ e : ↥(O.toricPts m) ≃+ (characterLattice ↥O.ssFinset →+ Additive ↥(rootsOfUnity m (AlgebraicClosure ℚ))),

      (∀ (χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A) (wb : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ),
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.toRingHom)) ≫ (O.toricLift m hm).1 ≫
            pullback.fst O.g Λ.σA = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1 →
        ∃ hx : O.toricPoint m hm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χ) ∈ O.toricPts m,
          ∀ a : characterLattice ↥O.ssFinset, ∃ u : ↥A,
            (u : AlgebraicClosure ℚ) = (((Additive.toMul (e ⟨_, hx⟩ a) : ↥(rootsOfUnity m (AlgebraicClosure ℚ))) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∧
            IsLocalRing.residue ↥A u = ((evalHom a (fun s => Additive.toMul (wb s)) : (ResidueField ↥A)ˣ) : ResidueField ↥A)) ∧

      (∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A, ∃ wb : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ,
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.toRingHom)) ≫ (O.toricLift m hm).1 ≫
            pullback.fst O.g Λ.σA = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1) ∧

      (∀ (φ : SchemeHomOver O.g O.g)
        (hφmul : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
          NeronModelInfra.schemeHomOverComp (O.L.mul s x y) φ =
            O.L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))
        (f : characterLattice ↥O.ssFinset →ₗ[ℤ] characterLattice ↥O.ssFinset)
        (op : (↥O.ssFinset → Additive (ResidueField ↥A)ˣ) →+ (↥O.ssFinset → Additive (ResidueField ↥A)ˣ))
        (hadj : ∀ (a : characterLattice ↥O.ssFinset) (w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ),
          evalHom (f a) (fun s => Additive.toMul (w s)) = evalHom a (fun s => Additive.toMul (op w s)))
        (hφ : ∀ w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ,
          O.ptsSp.symm (NeronModelInfra.schemeHomOverComp (O.ptsSp (GluedPic0.nodeUnit O.ssFinset w)) φ) =
            GluedPic0.nodeUnit O.ssFinset (op w))
        (hφtor : ∃ ψ : SchemeHomOver (muStr ↥A O.toricRank m) (muStr ↥A O.toricRank m),
          NeronModelInfra.schemeHomOverComp ψ (O.toricLift m hm) =
            NeronModelInfra.schemeHomOverComp (O.toricLift m hm) (fibreRestrictAlong Λ.σA O.g O.g φ)),
        ∀ x : ↥(O.toricPts m),
          ∃ hx : O.pts.symm (NeronModelInfra.schemeHomOverComp (O.pts (x : JH M H)) φ) ∈ O.toricPts m,
            e ⟨_, hx⟩ = (e x).comp f.toAddMonoidHom) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_toricPts_characterLattice_hom_of_ptsSp_nodeUnit.solution
