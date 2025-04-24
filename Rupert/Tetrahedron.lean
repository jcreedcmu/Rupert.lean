import Rupert.Basic
import Rupert.Convex
import Rupert.Quaternion

namespace Tetrahedron

open scoped Matrix

def tetrahedron : Fin 4 → ℝ³ := ![
  ![ 1,  1,  1],
  ![ 1, -1, -1],
  ![-1,  1, -1],
  ![-1, -1,  1]]

def outer_quat : Quaternion ℝ :=
  ⟨0.3389904789675945, -0.4261829733457893, 0.1736023394555525, -0.8205581978964213⟩

noncomputable def outer_rot := matrix_of_quat outer_quat

lemma outer_rot_so3 : outer_rot ∈ SO3 := by
  have orthogonal : outer_rot ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
    dsimp only [outer_rot, matrix_of_quat, outer_quat]
    norm_num1
    constructor
    · ext i j
      fin_cases i, j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
    · ext i j; fin_cases i, j <;> norm_num [Matrix.vecMul]
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨orthogonal, ?_⟩
  dsimp only [outer_rot, matrix_of_quat, outer_quat]
  norm_num1
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_three, Fin.succAbove]
  norm_num

def inner_quat : Quaternion ℝ :=
  ⟨0.8577016212029301, -0.1191615236085398, 0.4439711748359327, 0.2302999265999848⟩

noncomputable def inner_rot := matrix_of_quat inner_quat

lemma inner_rot_so3 : inner_rot ∈ SO3 := by
  have orthogonal : inner_rot ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
    dsimp only [inner_rot, matrix_of_quat, inner_quat]
    norm_num1
    constructor
    · ext i j
      fin_cases i, j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
    · ext i j; fin_cases i, j <;> norm_num [Matrix.vecMul]
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨orthogonal, ?_⟩
  dsimp only [inner_rot, matrix_of_quat, inner_quat]
  norm_num1
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_three, Fin.succAbove]
  norm_num

def inner_offset : ℝ² := ![0.09841265604345877,-0.165800542996898]

theorem rupert : IsRupert tetrahedron := by
  use outer_rot, outer_rot_so3, inner_rot, inner_rot_so3, inner_offset
  intro outer_shadow inner_shadow
  let ε₀ : ℝ := 0.001
  have hε₀ : ε₀ ∈ Set.Ioo 0 1 := by norm_num
  have hb : Metric.ball 0 ε₀ ⊆ convexHull ℝ outer_shadow := by
    refine ball_in_hull_of_corners_in_hull hε₀ ?_ ?_ ?_ ?_
    · sorry
    · sorry
    · sorry
    · sorry
  intro v hv
  let ε₁ : ℝ := 0.00001
  have hε₁ : ε₁ ∈ Set.Ioo 0 1 := by norm_num
  refine mem_interior_hull hε₀.1 hε₁ hb ?_
  simp only [Set.mem_range, inner_shadow] at hv
  obtain ⟨y, hy⟩ := hv
  rw [mem_convexHull_iff_exists_fintype]
  fin_cases y <;>
    simp only [tetrahedron, Fin.reduceFinMk, Matrix.cons_val, inner_shadow] at hy <;>
    use Fin 4, inferInstance
  · use ![24419762003513985479446993192034104101803115609735060626411685853698932075803/
          5094134272401397362124160033006247763499653762616164782597202714604400000000000,
          230409983468138546843093944744735640055655643438309323417206877017616228497521/
          48111268128235419531172622533947895544163396646930445168973581193486000000000000,
          0,
          26803252720787927505825797680094096268019775262787608903547648471915690294817441/
          27062588322132423486284600175345691243591910613898375407547639421335875000000000]
    use fun i ↦ (1 - ε₁) • (dropz (outer_rot *ᵥ (tetrahedron i)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_four]; simp; norm_num
    · intro i
      fin_cases i
      · use dropz (outer_rot *ᵥ tetrahedron 0); simp [outer_shadow]
      · use dropz (outer_rot *ᵥ tetrahedron 1); simp [outer_shadow]
      · use dropz (outer_rot *ᵥ tetrahedron 2); simp [outer_shadow]
      · use dropz (outer_rot *ᵥ tetrahedron 3); simp [outer_shadow]
    · simp [Fin.sum_univ_four]
      rw [←hy]
      simp [tetrahedron, dropz, outer_rot, matrix_of_quat, outer_quat,
            inner_offset, inner_rot, inner_quat]
      norm_num
      ext i
      fin_cases i
      · simp; norm_num
      · simp; norm_num
  · use ![4183611374521617762351928650236500798224660804096493226244818085853698932075803/
          5094134272401397362124160033006247763499653762616164782597202714604400000000000,
          25102339214950593199584615702794485893116570304996511060364674831052848685492563/
          144333804384706258593517867601843686632490189940791335506920743580458000000000000,
          0,
          130464292183092898867863776690314648064043159948909319303666809415690294817441/
          27062588322132423486284600175345691243591910613898375407547639421335875000000000]
    use fun i ↦ (1 - ε₁) • (dropz (outer_rot *ᵥ (tetrahedron i)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_four]; simp; norm_num
    · intro i
      fin_cases i
      · use dropz (outer_rot *ᵥ tetrahedron 0); simp [outer_shadow]
      · use dropz (outer_rot *ᵥ tetrahedron 1); simp [outer_shadow]
      · use dropz (outer_rot *ᵥ tetrahedron 2); simp [outer_shadow]
      · use dropz (outer_rot *ᵥ tetrahedron 3); simp [outer_shadow]
    · simp [Fin.sum_univ_four]
      rw [←hy]
      simp [tetrahedron, dropz, outer_rot, matrix_of_quat, outer_quat,
            inner_offset, inner_rot, inner_quat]
      norm_num
      ext i
      fin_cases i
      · simp; norm_num
      · simp; norm_num
  · use ![8149233408515772505369007668071732737002684771295565308694441951232977358601/
          1698044757467132454041386677668749254499884587538721594199067571534800000000000,
          142949325340764770430692464525851563328993579567048454817611738831052848685492563/
          144333804384706258593517867601843686632490189940791335506920743580458000000000000,
          0,
          14412379254534322913938279670958875434403795170474117459791191323965588313049/
          3006954258014713720698288908371743471510212290433152823060848824592875000000000]
    use fun i ↦ (1 - ε₁) • (dropz (outer_rot *ᵥ (tetrahedron i)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_four]; simp; norm_num
    · intro i
      fin_cases i
      · use dropz (outer_rot *ᵥ tetrahedron 0); simp [outer_shadow]
      · use dropz (outer_rot *ᵥ tetrahedron 1); simp [outer_shadow]
      · use dropz (outer_rot *ᵥ tetrahedron 2); simp [outer_shadow]
      · use dropz (outer_rot *ᵥ tetrahedron 3); simp [outer_shadow]
    · simp [Fin.sum_univ_four]
      rw [←hy]
      simp [tetrahedron, dropz, outer_rot, matrix_of_quat, outer_quat,
            inner_offset, inner_rot, inner_quat]
      norm_num
      ext i
      fin_cases i
      · simp; norm_num
      · simp; norm_num
  · use ![85389834878147286665060941385126660155497490856303099963877032772524468001547/
          103961923926559129839268572102168321704074566584003362910146994175600000000000,
          14144294721423687846667989826219510591782196043919743728224535327609156846787/
          2945587844585842012112609542894769114948779386546761949120831501642000000000000,
          0,
          96012167809420975391727790091867668740856553045172694953017069579912046833009/
          552297720859845377271114289292769209052896134977517865460155906557875000000000]
    use fun i ↦ (1 - ε₁) • (dropz (outer_rot *ᵥ (tetrahedron i)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_four]; simp; norm_num
    · intro i
      fin_cases i
      · use dropz (outer_rot *ᵥ tetrahedron 0); simp [outer_shadow]
      · use dropz (outer_rot *ᵥ tetrahedron 1); simp [outer_shadow]
      · use dropz (outer_rot *ᵥ tetrahedron 2); simp [outer_shadow]
      · use dropz (outer_rot *ᵥ tetrahedron 3); simp [outer_shadow]
    · simp [Fin.sum_univ_four]
      rw [←hy]
      simp [tetrahedron, dropz, outer_rot, matrix_of_quat, outer_quat,
            inner_offset, inner_rot, inner_quat]
      norm_num
      ext i
      fin_cases i
      · simp; norm_num
      · simp; norm_num

/-
-------------------------------------

Below we compute the coefficients...

-/

namespace Coeff

def tetrahedron : Fin 4 → EuclideanSpace ℚ (Fin 3) := ![
  ![ 1,  1,  1],
  ![ 1, -1, -1],
  ![-1,  1, -1],
  ![-1, -1,  1]]

def outer_quat : Quaternion ℚ :=
  ⟨0.3389904789675945, -0.4261829733457893, 0.1736023394555525, -0.8205581978964213⟩

def outer_rot := matrix_of_quat outer_quat

def inner_quat : Quaternion ℚ :=
  ⟨0.8577016212029301, -0.1191615236085398, 0.4439711748359327, 0.2302999265999848⟩

def inner_rot := matrix_of_quat inner_quat

def inner_offset : EuclideanSpace ℚ (Fin 2) := ![0.09841265604345877,-0.165800542996898]

def ε₁ : ℚ := 0.00001

open scoped Matrix

#eval fun i ↦ (1 - ε₁) • (dropz (outer_rot *ᵥ (tetrahedron i)))
/-
![![(2046374534559867373214391065442134733 : Rat)/2500000000000000658609538959436700000,
    (-3525336312241614680105804688074985933 : Rat)/2500000000000000658609538959436700000],
  ![(-4080889473201659924135204962204588473 : Rat)/2500000000000000658609538959436700000,
    (3893749672923670379042406623951043 : Rat)/2500000000000000658609538959436700000],
  ![(-663485556854645419112447097154599 : Rat)/357142857142857236944219851348100000,
    (-3443574576985150801999134796270569 : Rat)/357142857142857236944219851348100000],
  ![(2039159337539775068854601026442535933 : Rat)/2500000000000000658609538959436700000,
    (3545547584607587065340756225024928873 : Rat)/2500000000000000658609538959436700000]]

p1 = vector(QQ, [2046374534559867373214391065442134733/2500000000000000658609538959436700000,
                 -3525336312241614680105804688074985933/2500000000000000658609538959436700000])
p2 = vector(QQ, [-4080889473201659924135204962204588473/2500000000000000658609538959436700000,
                  3893749672923670379042406623951043/2500000000000000658609538959436700000])
p3 = vector(QQ, [-663485556854645419112447097154599/357142857142857236944219851348100000,
                 -3443574576985150801999134796270569/357142857142857236944219851348100000])
p4 = vector(QQ, [2039159337539775068854601026442535933/2500000000000000658609538959436700000,
                 3545547584607587065340756225024928873/2500000000000000658609538959436700000])
-/

def hack_add (v1 v2 : EuclideanSpace ℚ (Fin 2)) : EuclideanSpace ℚ (Fin 2) :=
  ![v1 0 + v2 0, v1 1 + v2 1]

#eval fun i ↦ hack_add inner_offset (dropz (inner_rot *ᵥ (tetrahedron i)))
/-
![![(4019768719886866306784863677837758422155311667163 : Rat)/4999999999999999440740553764151900000000000000000,
    (34946905166908186857695936394343991216473495969 : Rat)/24999999999999997203702768820759500000000000000],
  ![(1961388635004586013639940024331958422155311667163 : Rat)/4999999999999999440740553764151900000000000000000,
    (-28774498439153123623204462034761008783526504031 : Rat)/24999999999999997203702768820759500000000000000],
  ![(-2681433400080399000741852863814680525948229444279 : Rat)/1666666666666666480246851254717300000000000000000,
    (13105064393403673628838342049330405491165323 : Rat)/8333333333333332401234256273586500000000000000],
  ![(4031395966218919861647924803419358422155311667163 : Rat)/4999999999999999440740553764151900000000000000000,
    (-22791776220625072400867592144769008783526504031 : Rat)/24999999999999997203702768820759500000000000000]]

q = vector(QQ, [4031395966218919861647924803419358422155311667163/4999999999999999440740553764151900000000000000000,
                -22791776220625072400867592144769008783526504031/24999999999999997203702768820759500000000000000])

-/
