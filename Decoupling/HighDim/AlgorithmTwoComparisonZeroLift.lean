import Decoupling.HighDim.AlgorithmTwoComparisonZeroModel

/-!
# A prescribed comparison through a zero-differential model

The only isomorphism premise is the formal derived isomorphism in the
algorithm input. No comparison cochain map, boundary, or homotopy is
supplied. The source augmentation is a genuine quasi-isomorphism, and
the desired coordinates are native cohomology coordinates.
-/
namespace Decoupling.HighDim.AlgorithmTwoComparison
open CategoryTheory HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
attribute [local instance] HasDerivedCategory.standard
variable {R : Type} [CommRing R]
variable {T V C : CochainComplex (ModuleCat R) ℤ}
  (hz : ∀ i j, V.d i j = 0) (q : T ⟶ V) [QuasiIso q]
  (e : DerivedCategory.Q.obj T ≅ DerivedCategory.Q.obj C)
  (b : ∀ n, V.X n ≅ C.homology n)

def zeroComparisonIso : DerivedCategory.Q.obj T ≅ DerivedCategory.Q.obj C :=
  asIso (DerivedCategory.Q.map q) ≪≫
    zeroNormalizedIso V hz ((asIso (DerivedCategory.Q.map q)).symm ≪≫ e) b

theorem zeroComparison_homology (g : T ⟶ C)
    (hg : DerivedCategory.Q.map g = (zeroComparisonIso hz q e b).hom) (n : ℤ) :
    homologyMap q n ≫ (zeroClassIso V hz n).inv ≫ (b n).hom = homologyMap g n := by
  let H := DerivedCategory.homologyFunctor (ModuleCat R) n
  let F := DerivedCategory.homologyFunctorFactors (ModuleCat R) n
  let a := zeroNormalizedIso V hz ((asIso (DerivedCategory.Q.map q)).symm ≪≫ e) b
  have hnorm : (zeroClassIso V hz n).hom ≫ (F.app V).inv ≫ H.map a.hom ≫ (F.app C).hom =
      (b n).hom := zeroNormalizedIso_homology V hz _ b n
  have hq : homologyMap q n ≫ (F.app V).inv =
      (F.app T).inv ≫ H.map (DerivedCategory.Q.map q) := F.inv.naturality q
  have hgn : H.map (DerivedCategory.Q.map g) ≫ (F.app C).hom =
      (F.app T).hom ≫ homologyMap g n := F.hom.naturality g
  rw [← hnorm]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Category.assoc (homologyMap q n), hq]
  simp only [Category.assoc]
  rw [← Category.assoc (H.map (DerivedCategory.Q.map q)), ← H.map_comp]
  have he : DerivedCategory.Q.map q ≫ a.hom = DerivedCategory.Q.map g := hg.symm
  rw [he, hgn]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem zeroComparison_cycle (g : T ⟶ C)
    (hg : DerivedCategory.Q.map g = (zeroComparisonIso hz q e b).hom)
    (n : ℤ) (x : T.X n) (hx : T.d n (n + 1) x = 0) :
    nativeCycleClass C n (g.f n x) (by
      change (g.f n ≫ C.d n (n + 1)) x = 0
      rw [g.comm]
      change g.f (n + 1) (T.d n (n + 1) x) = 0
      rw [hx, map_zero]) =
      (b n).hom (q.f n x) := by
  rw [← nativeCycleClass_naturality]
  rw [← zeroComparison_homology hz q e b g hg n]
  change (b n).hom ((zeroClassIso V hz n).inv
    (homologyMap q n (nativeCycleClass T n x hx))) = _
  rw [nativeCycleClass_naturality, ← zeroClassIso_apply]
  change (b n).hom (((zeroClassIso V hz n).hom ≫ (zeroClassIso V hz n).inv) (q.f n x)) = _
  rw [Iso.hom_inv_id]
  rfl

theorem exists_zeroComparison [T.IsKProjective] :
    ∃ g : T ⟶ C, QuasiIso g ∧
      DerivedCategory.Q.map g = (zeroComparisonIso hz q e b).hom ∧
      ∀ n (x : T.X n) (hx : T.d n (n + 1) x = 0),
        homologyMap g n (nativeCycleClass T n x hx) = (b n).hom (q.f n x) := by
  obtain ⟨g, hg⟩ := exists_cochain_lift (zeroComparisonIso hz q e b).hom
  have hq : QuasiIso g := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) g).mp
    rw [hg]
    infer_instance
  refine ⟨g, hq, hg, ?_⟩
  intro n x hx
  rw [nativeCycleClass_naturality]
  exact zeroComparison_cycle hz q e b g hg n x hx

end
end Decoupling.HighDim.AlgorithmTwoComparison
