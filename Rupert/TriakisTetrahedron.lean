import Rupert.Basic
import Rupert.Convex
import Rupert.MatrixSimps
import Rupert.Quaternion
import Rupert.RelatingRupertDefs

namespace TriakisTetrahedron

open scoped Matrix

/- This is the tom7's triakis tetrahedron scaled by 3/5, so that
   the first four vertices make up a regular tetrahedron with nice unit
   coordinates, and the remaining vertices represent the augmentations
   of each of the faces of that tetrahedron. -/

noncomputable def vertices : Fin 8 → ℝ³ :=
  ![![   1,    1,    1],
    ![   1,   -1,   -1],
    ![  -1,    1,   -1],
    ![  -1,   -1,    1],
    ![-3/5,  3/5,  3/5],
    ![ 3/5, -3/5,  3/5],
    ![ 3/5,  3/5, -3/5],
    ![-3/5, -3/5, -3/5]]

def outer_quat : Quaternion ℝ := ⟨0.858732110, -0.148912807, -0.352436516, -0.340870417⟩

noncomputable def outer_rot := matrix_of_quat outer_quat

lemma outer_rot_so3 : outer_rot ∈ SO3 := by
  have h : outer_quat.normSq ≠ 0 := by norm_num [outer_quat, Quaternion.normSq_def]
  exact matrix_of_quat_is_s03 h

def inner_quat : Quaternion ℝ := ⟨0.144873924, 0.365747659, -0.854692880, -0.338733344⟩

noncomputable def inner_rot := matrix_of_quat inner_quat

lemma inner_rot_so3 : inner_rot ∈ SO3 := by
  have h : inner_quat.normSq ≠ 0 := by norm_num [inner_quat, Quaternion.normSq_def]
  exact matrix_of_quat_is_s03 h

def inner_offset : ℝ² := ![8.5629464761e-05, 8.9387250451e-05]

set_option maxHeartbeats 207000 in
theorem rupert : IsRupert vertices := by
  rw [rupert_iff_rupert']
  use inner_rot, inner_rot_so3, inner_offset, outer_rot, outer_rot_so3
  intro inner_shadow outer_shadow
  let ε₀ : ℝ := 0.006
  have hε₀ : ε₀ ∈ Set.Ioo 0 1 := by norm_num
  have hb : Metric.ball 0 ε₀ ⊆ convexHull ℝ outer_shadow := by
    refine Convex.ball_in_hull_of_corners_in_hull hε₀ ?_ ?_ ?_ ?_ <;>
      apply mem_convexHull_iff_exists_fintype.mpr <;>
      use Fin 8, inferInstance
    · use ![0, 0, 0,
            209107410810126884571/565617601328354816800,
            245824061168864729/35351100083022176050,
            0,
            70515401107905219313/113123520265670963360,
            0]
      use fun i ↦ proj_xy (outer_rot *ᵥ vertices i)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> norm_num
      · simp [Fin.sum_univ_eight]; norm_num
      · exact fun i ↦ ⟨i, rfl⟩
      · simp only [proj_xy, outer_rot, matrix_of_quat, outer_quat, vertices,
                   Fin.sum_univ_eight, ε₀, outer_shadow, matrix_simps]
        norm_num
    · use ![0,
            1051981313303264779479/2828088006641774084000,
            0,
            19719000787634436/6798288477504264625,
            353580717802170675829/565617601328354816800,
            0, 0, 0]
      use fun i ↦ proj_xy (outer_rot *ᵥ vertices i)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> norm_num
      · simp [Fin.sum_univ_eight]; norm_num
      · exact fun i ↦ ⟨i, rfl⟩
      · simp only [proj_xy, outer_rot, matrix_of_quat, outer_quat, vertices,
                   Fin.sum_univ_eight, ε₀, outer_shadow, matrix_simps]
        norm_num
    · use ![3938334956654107739/8031045263445271000,
            2045224314929433491/8031045263445271000,
            0,
            204748599186172977/803104526344527100,
            0, 0, 0, 0]
      use fun i ↦ proj_xy (outer_rot *ᵥ vertices i)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> norm_num
      · simp [Fin.sum_univ_eight]; norm_num
      · exact fun i ↦ ⟨i, rfl⟩
      · simp only [proj_xy, outer_rot, matrix_of_quat, outer_quat, vertices,
                   Fin.sum_univ_eight, ε₀, outer_shadow, matrix_simps]
        norm_num
    · use ![0,
            1095105012905906001/353511000830221760500,
            0,
            1052120747247162610137/2828088006641774084000,
            0, 0,
            353441283858272845171/565617601328354816800,
            0]
      use fun i ↦ proj_xy (outer_rot *ᵥ vertices i)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> norm_num
      · simp [Fin.sum_univ_eight]; norm_num
      · exact fun i ↦ ⟨i, rfl⟩
      · simp only [proj_xy, outer_rot, matrix_of_quat, outer_quat, vertices,
                   Fin.sum_univ_eight, ε₀, outer_shadow, matrix_simps]
        norm_num
  intro v hv
  let ε₁ : ℝ := 1e-11
  have hε₁ : ε₁ ∈ Set.Ioo 0 1 := by norm_num
  refine Convex.mem_interior_hull hε₀.1 hε₁ hb ?_
  simp only [Set.mem_range, inner_shadow] at hv
  obtain ⟨y, hy⟩ := hv
  rw [mem_convexHull_iff_exists_fintype]
  fin_cases y <;>
    simp only [vertices, Fin.reduceFinMk, Matrix.cons_val, inner_shadow] at hy <;>
    use Fin 8, inferInstance
  · use ![320050956502833201167751985054675539223111361/
          158836228761182627011085302790150062539835294740000,
          37478789684155822552149249633100762035628799779/
          158836228761182627011085302790150062539835294740000,
          0,
          2646640498675699472588866429808865118371007380481/
          2647270479353043783518088379835834375663921579000,
          0, 0, 0, 0]
    use fun i ↦ (1 - ε₁) • (proj_xy (outer_rot *ᵥ vertices i))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · simp only [Fin.sum_univ_eight, matrix_simps]; norm_num
    · exact fun i ↦ ⟨proj_xy (outer_rot *ᵥ vertices i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [proj_xy, outer_rot, matrix_of_quat, outer_quat, vertices,
        Fin.sum_univ_eight, inner_offset, inner_rot, inner_quat, ε₁, inner_shadow,
        outer_shadow, matrix_simps]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num
  · use ![2690065380721338931107844675930079853008002249/
          1429526058850643643099767725111350562858517652660000,
          1429185801354497250493132886580886682858320659198011/
          1429526058850643643099767725111350562858517652660000,
          0,
          5626123846094521128395511429799165339066424329/
          23825434314177394051662795418522509380975294211000,
          0, 0, 0, 0]
    use fun i ↦ (1 - ε₁) • (proj_xy (outer_rot *ᵥ vertices i))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · simp only [Fin.sum_univ_eight, matrix_simps]; norm_num
    · exact fun i ↦ ⟨proj_xy (outer_rot *ᵥ vertices i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [proj_xy, outer_rot, matrix_of_quat, outer_quat, vertices,
        Fin.sum_univ_eight, inner_offset, inner_rot, inner_quat, ε₁, inner_shadow,
        outer_shadow, matrix_simps]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num
  · use ![282844578280123522478732365155221962237373746450249/
          298290854644984786267344341448022649016038391108000,
          0, 0, 0,
          1716079538871724601954309613272108094228427903699/
          33143428293887198474149371272002516557337599012000,
          0,
          78025750787118551159488667585696530439676223/
          14914542732249239313367217072401132450801919555400,
          0]
    use fun i ↦ (1 - ε₁) • (proj_xy (outer_rot *ᵥ vertices i))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · simp only [Fin.sum_univ_eight, matrix_simps]; norm_num
    · exact fun i ↦ ⟨proj_xy (outer_rot *ᵥ vertices i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [proj_xy, outer_rot, matrix_of_quat, outer_quat, vertices,
        Fin.sum_univ_eight, inner_offset, inner_rot, inner_quat, ε₁, inner_shadow,
        outer_shadow, matrix_simps]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num
  · use ![283117566838487610246913017563019376237373746450249/
          298290854644984786267344341448022649016038391108000,
          0, 0, 0,
          1574537650882650012051296636476848055851133291/
          298290854644984786267344341448022649016038391108000,
          0,
          758585663442314668520963629418339796530439676223/
          14914542732249239313367217072401132450801919555400,
          0]
    use fun i ↦ (1 - ε₁) • (proj_xy (outer_rot *ᵥ vertices i))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · simp only [Fin.sum_univ_eight, matrix_simps]; norm_num
    · exact fun i ↦ ⟨proj_xy (outer_rot *ᵥ vertices i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [proj_xy, outer_rot, matrix_of_quat, outer_quat, vertices,
        Fin.sum_univ_eight, inner_offset, inner_rot, inner_quat, ε₁, inner_shadow,
        outer_shadow, matrix_simps]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num
  · use ![15381264075549739501273188093551493041527383361/
          33143428293887198474149371272002516557337599012000,
          0, 0, 0,
          99383630567848375480456938122952631882685283711097/
          99430284881661595422448113816007549672012797036000,
          0,
          25526079328536174367806438713165510146558741/
          4971514244083079771122405690800377483600639851800,
          0]
    use fun i ↦ (1 - ε₁) • (proj_xy (outer_rot *ᵥ vertices i))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · simp only [Fin.sum_univ_eight, matrix_simps]; norm_num
    · exact fun i ↦ ⟨proj_xy (outer_rot *ᵥ vertices i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [proj_xy, outer_rot, matrix_of_quat, outer_quat, vertices,
        Fin.sum_univ_eight, inner_offset, inner_rot, inner_quat, ε₁, inner_shadow,
        outer_shadow, matrix_simps]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num
  · use ![31436375570010867744955561974649501075539223111361/
          158836228761182627011085302790150062539835294740000,
          65162484389967530498892502615908096362035628799779/
          158836228761182627011085302790150062539835294740000,
          0,
          3111868440060211438361861909979623255113022141443/
          7941811438059131350554265139507503126991764737000,
          0, 0, 0, 0]
    use fun i ↦ (1 - ε₁) • (proj_xy (outer_rot *ᵥ vertices i))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · simp only [Fin.sum_univ_eight, matrix_simps]; norm_num
    · exact fun i ↦ ⟨proj_xy (outer_rot *ᵥ vertices i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [proj_xy, outer_rot, matrix_of_quat, outer_quat, vertices,
        Fin.sum_univ_eight, inner_offset, inner_rot, inner_quat, ε₁, inner_shadow,
        outer_shadow, matrix_simps]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num
  · use ![31418176332786595227076851814129673475539223111361/
          158836228761182627011085302790150062539835294740000,
          62237357220617638995747652173682152362035628799779/
          158836228761182627011085302790150062539835294740000,
          0,
          1086344920129639879804346646705637278371007380481/
          2647270479353043783518088379835834375663921579000,
          0, 0, 0, 0]
    use fun i ↦ (1 - ε₁) • (proj_xy (outer_rot *ᵥ vertices i))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · simp only [Fin.sum_univ_eight, matrix_simps]; norm_num
    · exact fun i ↦ ⟨proj_xy (outer_rot *ᵥ vertices i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [proj_xy, outer_rot, matrix_of_quat, outer_quat, vertices,
        Fin.sum_univ_eight, inner_offset, inner_rot, inner_quat, ε₁, inner_shadow,
        outer_shadow, matrix_simps]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num
  · use ![46105713581088386527939179642742079124582150083/
          99430284881661595422448113816007549672012797036000,
          0, 0, 0,
          499295037844618876866011627687882685283711097/
          99430284881661595422448113816007549672012797036000,
          0,
          4969183993652133120852165431236855985510146558741/
          4971514244083079771122405690800377483600639851800,
          0]
    use fun i ↦ (1 - ε₁) • (proj_xy (outer_rot *ᵥ vertices i))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · simp only [Fin.sum_univ_eight, matrix_simps]; norm_num
    · exact fun i ↦ ⟨proj_xy (outer_rot *ᵥ vertices i), by simp [outer_shadow]⟩
    · rw [←hy]
      simp only [proj_xy, outer_rot, matrix_of_quat, outer_quat, vertices,
        Fin.sum_univ_eight, inner_offset, inner_rot, inner_quat, ε₁, inner_shadow,
        outer_shadow, matrix_simps]
      rw [Matrix.smul_vec2, Matrix.smul_vec2, Matrix.smul_vec2,
          Matrix.vec2_add, Matrix.vec2_add, Matrix.vec2_add]
      norm_num


/-
computing the coefficients...


namespace Coeff

def triakis_tetrahedron : Fin 8 → EuclideanSpace ℚ (Fin 3) :=
  ![![   1,    1,    1],
    ![   1,   -1,   -1],
    ![  -1,    1,   -1],
    ![  -1,   -1,    1],
    ![-3/5,  3/5,  3/5],
    ![ 3/5, -3/5,  3/5],
    ![ 3/5,  3/5, -3/5],
    ![-3/5, -3/5, -3/5]]

def outer_quat : Quaternion ℚ := ⟨0.858732110, -0.148912807, -0.352436516, -0.340870417⟩

def outer_rot := matrix_of_quat outer_quat

def inner_quat : Quaternion ℚ := ⟨0.144873924, 0.365747659, -0.854692880, -0.338733344⟩
def inner_rot := matrix_of_quat inner_quat

def inner_offset : EuclideanSpace ℚ (Fin 2) := ![8.5629464761e-05, 8.9387250451e-05]

def ε₁ : ℚ := 1e-11

open scoped Matrix

#eval fun i ↦ (1 - ε₁) • (proj_xy (outer_rot *ᵥ (triakis_tetrahedron i)))

/-
points = [
    vector(QQ, [35290596182217258338174298357/49999999991482174700000000000,
                36940966423270499635763600907/49999999991482174700000000000]),
    vector(QQ, [16628576001033470339988002439/49999999991482174700000000000,
                 -84987778730815923112683341991/49999999991482174700000000000]),
    vector(QQ, [33749140479862400695198001079/49999999991482174700000000000,
                56616800806553531991928803/79999999986371479520000000]),
    vector(QQ, [-137069300260981006997376483/79999999986371479520000000,
                12661311803449465981964239209/49999999991482174700000000000]),
    vector(QQ, [-49885728003100411019964007317/249999999957410873500000000000,
                254963336192447769338050025973/249999999957410873500000000000]),
    vector(QQ, [-101247421439587202085594003237/249999999957410873500000000000,
                -169850402419660595975786409/399999999931857397600000000]),
    vector(QQ, [411207900782943020992129449/399999999931857397600000000,
                -37983935410348397945892717627/249999999957410873500000000000]),
    vector(QQ, [-105871788546651775014522895071/249999999957410873500000000000,
                -110822899269811498907290802721/249999999957410873500000000000])
]
-/

--#eval fun i ↦ (proj_xy (outer_rot *ᵥ (triakis_tetrahedron i)))

/-
points = [
  vector(QQ, [352905961825701643/499999999914821747,
              369409664236399093/499999999914821747]),
  vector(QQ, [166285760011997561/499999999914821747,
              -849877787316658009/499999999914821747]),
  vector(QQ, [337491404801998921/499999999914821747,
              353855005044498125/499999999914821747]),
  vector(QQ, [-856683126639698125/499999999914821747,
              126613118035760791/499999999914821747]),
  vector(QQ, [-498857280035992683/2499999999574108735,
              2549633361949974027/2499999999574108735]),
  vector(QQ, [-1012474214405996763/2499999999574108735,
              -212313003026698875/499999999914821747]),
  vector(QQ, [514009875983818875/499999999914821747,
              -379839354107282373/2499999999574108735]),
  vector(QQ, [-1058717885477104929/2499999999574108735,
              -1108228992709197279/2499999999574108735])
]

-/

def hack_add (v1 v2 : EuclideanSpace ℚ (Fin 2)) : EuclideanSpace ℚ (Fin 2) :=
  ![v1 0 + v2 0, v1 1 + v2 1]

#eval fun i ↦ hack_add inner_offset (proj_xy (inner_rot *ᵥ (triakis_tetrahedron i)))

/-
[-570959541507199111383435455383509/333333333793084931000000000000000,
  84255463957912634264539211053881/333333333793084931000000000000000]

  [332089096369398185849693633849473/1000000001379254793000000000000000,
   -1699289812408148431206382366838357/1000000001379254793000000000000000]

  [658936718295171287849693633849473/1000000001379254793000000000000000,
   753365871780309790793617633161643/1000000001379254793000000000000000]

  [722195327716544279849693633849473/1000000001379254793000000000000000,
   693515097756397888793617633161643/1000000001379254793000000000000000]

  [-66372150225944114583435455383509/333333333793084931000000000000000,
   339905635681935973064539211053881/333333333793084931000000000000000]

  [-131741674611098734983435455383509/333333333793084931000000000000000,
   -150625501155755671335460788946119/333333333793084931000000000000000]

  [-144393396495373333383435455383509/333333333793084931000000000000000,
   -138655346350973290935460788946119/333333333793084931000000000000000]


  [342621393952254989416564544616491/333333333793084931000000000000000,
   -50505605174441293735460788946119/333333333793084931000000000000000]

-/

-/
