import ZT5A

/-!
# Statement of the p. 428 coercivity lemma (Balaban, CMP 99b)

This file only displays the statement `AdalyFormal.StatementLaneG.P428Target8` and the definitions
it is built from.  It contains no theorem and no proof.  Compile it with `lake build StatementLib`
or `lake env lean Statement.lean`; the output is reproduced in `statement_output.txt`.
-/

set_option pp.proofs true
set_option pp.unicode.fun true

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2

/-! ## 1. The statement -/

#check @AdalyFormal.StatementLaneG.P428Target8
#print AdalyFormal.StatementLaneG.P428Target8

-- the statement for fixed ell, M = ell^m, R, a: side condition and constants block
#print AdalyFormal.StatementLaneG.P428Genuine8
#print AdalyFormal.StatementLaneG.SidePow6
#print AdalyFormal.StatementLaneG.P428Core8
#print AdalyFormal.StatementLaneG.P428Core8At

/-! ## 2. The claim at fixed depth k, torus Lu, cube factor c, class constant alpha_0, bound gamma_0 -/

#print AdalyFormal.StatementLaneG.CoercG8At

/-! ## 3. Lattice, scaling and the tower of domains Omega_j -/

#print AdalyFormal.Target.ClayStatement.PeriodicLatticeExtent
#print AdalyFormal.StatementLane.scaleUp
#print AdalyFormal.StatementLane.Tower
#print AdalyFormal.StatementLane.bigSide
#print AdalyFormal.StatementLane.pcd
#print AdalyFormal.StatementLane.pdist
#print AdalyFormal.StatementLane.BlockClosed
#print AdalyFormal.StatementLane.Admissible

/-! ## 4. Torus condition -/

#print AdalyFormal.StatementLane.TorusOK

/-! ## 5. The region Lambda (Lambda = B(Lambda')) -/

#print AdalyFormal.StatementLane.LambdaOK
#print AdalyFormal.StatementLaneG.LamBlockSum
#print AdalyFormal.StatementLaneG.LambdaOK2
#print AdalyFormal.StatementLane.LamPrime

/-! ## 6. Class cubes (DescribedAt) -/

#print AdalyFormal.StatementLane.towerBj
#print AdalyFormal.StatementLane.siteBox
#print AdalyFormal.StatementLane.GridCorner
#print AdalyFormal.StatementLane.DescribedAt
#print AdalyFormal.StatementLane.IsClassCube
#print AdalyFormal.StatementLane.CubeBond

/-! ## 7. The class-coupling hypothesis on the background field U -/

#print AdalyFormal.StatementLane2.ClassCoupled
#print AdalyFormal.StatementLane2.CoversOm0p
#print AdalyFormal.StatementLane2.CoversOm0c
#print AdalyFormal.StatementLane2.CoversPlaqOm0c
#print AdalyFormal.StatementLane2.PerCubeRegular2
#print AdalyFormal.StatementLane2.PlaqGaugeAt

/-! ## 8. The regularity predicate: Hermitian-traceless, discrete derivatives -/

#print AdalyFormal.StatementLane.HT
#print AdalyFormal.StatementLane2.ddA
#print AdalyFormal.StatementLane2.curlA
#print AdalyFormal.StatementLane2.CurlReads

/-! ## 9. The set of test fields B~ in Lambda~ and the touching-bond convention -/

#print AdalyFormal.StatementLane.OnLambdaTildeIn
#print AdalyFormal.StatementLane.IsDroppedIn
#print AdalyFormal.StatementLane.CRowIn
#print AdalyFormal.StatementLane2.OnLambdaT

/-! ## 10. The inequality predicate -/

#print AdalyFormal.StatementLaneG.InstIneq
#print AdalyFormal.Balaban.RegularUPerturbation.bondEnergy

/-! ## 11. The quadratic form genForm and the operator C -/

#print AdalyFormal.StatementLaneG.gparams
#print AdalyFormal.IngredientFamilyR2.IngrBParams
#print AdalyFormal.StatementLaneG.GenP.genForm
#print AdalyFormal.StatementLaneG.GenP.firstTerm
#print AdalyFormal.StatementLaneG.GenP.Nmat
#print AdalyFormal.StatementLaneG.GenP.genC

/-! ## 12. Operators entering genForm: G1, Q, H1, D2, J, and the constraint operator C = 1 - h Q -/

#print AdalyFormal.IngredientFamilyR2.IngrBParams.Jf
#print AdalyFormal.IngredientFamilyR2.IngrBParams.data
#print AdalyFormal.IngredientFamilyR2.IngrBParams.G1inv
#print AdalyFormal.IngredientFamilyR2.IngrBParams.Q1
#print AdalyFormal.IngredientFamilyR2.IngrBParams.unitBgU
#print AdalyFormal.IngredientFamilyR2.IngrBParams.tau
#print AdalyFormal.IngredientFamilyR2.IngrBParams.Qin
#print AdalyFormal.IngredientFamilyR2.IngrBParams.H1in
#print AdalyFormal.IngredientFamilyR2.IngrBParams.D2in
#print AdalyFormal.IngredientFamilyR2.H0
#print AdalyFormal.IngredientFamilyR2.H0inv
#print AdalyFormal.IngredientFamilyR2.hLift
#print AdalyFormal.IngredientFamilyR2.Cop

/-! ## 13. The operator Delta (3.10) and the source J (3.11), localised to the plaquettes of Omega_0 -/

#print AdalyFormal.IngredientFamilyR2.plaqIn
#print AdalyFormal.IngredientFamilyR2.Delta
#print AdalyFormal.IngredientFamilyR2.DpiFull
#print AdalyFormal.IngredientFamilyR2.Tfull
