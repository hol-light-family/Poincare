(* ========================================================================= *)
(* pc_moi_s32_cell: the main theorem CELL = MOI_S32_CELL (Moise p.227, end   *)
(* of the proof of 32.1): the annular chain plus the centre is an open       *)
(* 2-cell whose closure adds exactly the rim, locally polyhedral off the     *)
(* centre; the chain lies in g(0) INSERT g(v).  Route: compatible            *)
(* parametrizations of the bi-infinite chain of annuli by the square         *)
(* annulus, glued over the locally finite pieces off the centre into a       *)
(* homeomorphism of the open unit square onto the chain plus its limit point *)
(* (MOI_S3CL_CHAIN_DISK).                                                    *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_s32_gfacts.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Part 1: infnorm annuli of real^2.  The radial extension of a             *)
(* homeomorphism of the unit infnorm circle to every annulus                 *)
(* (MOI_S3CL_RAD_HOMEO), the radial affine maps between annuli               *)
(* (MOI_S3CL_SCL_HOMEO), the square annulus of pl_annulus_with_ends as an    *)
(* infnorm annulus, and the re-parametrization steps that make two annuli   *)
(* with a shared circle agree on it (MOI_S3CL_STEP_FWD, MOI_S3CL_STEP_BWD).  *)
(* ========================================================================= *)

let moi_s3cl_sann = new_definition
 `moi_s3cl_sann (a:real) (b:real) = {z:real^2 | a <= infnorm z /\ infnorm z <= b}`;;

let moi_s3cl_rad = new_definition
 `moi_s3cl_rad (tau:real^2->real^2) (z:real^2) = infnorm z % tau(inv(infnorm z) % z)`;;

let moi_s3cl_scl = new_definition
 `moi_s3cl_scl (a:real) (b:real) (c:real) (d:real) (z:real^2) =
    (c + (infnorm z - a) * (d - c) / (b - a)) % (inv(infnorm z) % z)`;;

let MOI_S3CL_INFNORM_CONT = prove
 (`!s:real^N->bool. (lift o infnorm) continuous_on s`,
  GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REWRITE_TAC[CONTINUOUS_AT_LIFT_INFNORM]);;

let MOI_S3CL_DIR_CONT = prove
 (`!s:real^N->bool. ~(vec 0 IN s) ==> (\z. inv(infnorm z) % z) continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  REWRITE_TAC[CONTINUOUS_ON_ID] THEN
  SUBGOAL_THEN `(lift o (\z:real^N. inv(infnorm z))) = (lift o inv o infnorm)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_INV THEN REWRITE_TAC[MOI_S3CL_INFNORM_CONT] THEN
  REWRITE_TAC[INFNORM_EQ_0] THEN ASM_MESON_TAC[]);;

let MOI_S3CL_DIR_NORM = prove
 (`!z:real^N. ~(z = vec 0) ==> infnorm(inv(infnorm z) % z) = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INFNORM_MUL; REAL_ABS_INV; REAL_ABS_INFNORM] THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[INFNORM_EQ_0]);;

let MOI_S3CL_SANN_NZ = prove
 (`!a b z. &0 < a /\ z IN moi_s3cl_sann a b ==> ~(z = vec 0) /\ &0 < infnorm z`,
  REWRITE_TAC[moi_s3cl_sann; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < infnorm(z:real^2)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN UNDISCH_TAC `&0 < infnorm(z:real^2)` THEN
  ASM_REWRITE_TAC[INFNORM_0; REAL_LT_REFL]);;

(* Half of the radial extension: continuity, the image and the left inverse. *)

let MOI_S3CL_RAD_HALF = prove
 (`!t t' a b.
     &0 < a /\ (!w. w IN moi_s3cl_sann (&1) (&1) ==> t' (t w) = w) /\
     IMAGE t (moi_s3cl_sann (&1) (&1)) SUBSET moi_s3cl_sann (&1) (&1) /\
     t continuous_on moi_s3cl_sann (&1) (&1)
     ==> moi_s3cl_rad t continuous_on moi_s3cl_sann a b /\
         IMAGE (moi_s3cl_rad t) (moi_s3cl_sann a b) SUBSET moi_s3cl_sann a b /\
         (!z. z IN moi_s3cl_sann a b ==> moi_s3cl_rad t' (moi_s3cl_rad t z) = z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN moi_s3cl_sann a b
                    ==> ~(z = vec 0) /\ &0 < infnorm z /\
                        inv(infnorm z) % z IN moi_s3cl_sann (&1) (&1)`
  (LABEL_TAC "dir") THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a:real`; `b:real`; `z:real^2`] MOI_S3CL_SANN_NZ) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[moi_s3cl_sann; IN_ELIM_THM] THEN ASM_SIMP_TAC[MOI_S3CL_DIR_NORM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN moi_s3cl_sann a b ==> infnorm(moi_s3cl_rad t z) = infnorm z`
  (LABEL_TAC "nrm") THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    USE_THEN "dir" (MP_TAC o C MP (ASSUME `(z:real^2) IN moi_s3cl_sann a b`) o
                    SPEC `z:real^2`) THEN STRIP_TAC THEN
    REWRITE_TAC[moi_s3cl_rad; INFNORM_MUL; REAL_ABS_INFNORM] THEN
    SUBGOAL_THEN `infnorm((t:real^2->real^2) (inv(infnorm z) % z)) = &1`
    (fun th -> REWRITE_TAC[th; REAL_MUL_RID]) THEN
    SUBGOAL_THEN `(t:real^2->real^2) (inv(infnorm z) % z) IN moi_s3cl_sann (&1) (&1)`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[moi_s3cl_sann; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `moi_s3cl_rad t = (\z. infnorm z % (t:real^2->real^2)(inv(infnorm z) % z))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_s3cl_rad]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[MOI_S3CL_INFNORM_CONT] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3CL_DIR_CONT THEN
      DISCH_THEN(fun th -> USE_THEN "dir" (MP_TAC o C MP th o SPEC `vec 0:real^2`)) THEN
      REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `moi_s3cl_sann (&1) (&1)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    USE_THEN "nrm" (MP_TAC o C MP (ASSUME `(z:real^2) IN moi_s3cl_sann a b`) o
                    SPEC `z:real^2`) THEN
    UNDISCH_TAC `(z:real^2) IN moi_s3cl_sann a b` THEN
    REWRITE_TAC[moi_s3cl_sann; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    USE_THEN "dir" (MP_TAC o C MP (ASSUME `(z:real^2) IN moi_s3cl_sann a b`) o
                    SPEC `z:real^2`) THEN STRIP_TAC THEN
    USE_THEN "nrm" (ASSUME_TAC o C MP (ASSUME `(z:real^2) IN moi_s3cl_sann a b`) o
                    SPEC `z:real^2`) THEN
    GEN_REWRITE_TAC LAND_CONV [moi_s3cl_rad] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv(infnorm z) % (moi_s3cl_rad t z) = (t:real^2->real^2) (inv(infnorm z) % z)`
    SUBST1_TAC THENL
     [REWRITE_TAC[moi_s3cl_rad; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]]);;

(* A homeomorphism tau of the unit infnorm circle extends radially to every *)
(* annulus a <= infnorm z <= b (0 < a): z = t w goes to t tau(w).            *)

let MOI_S3CL_RAD_HOMEO = prove
 (`!tau tau' a b.
     &0 < a /\
     homeomorphism (moi_s3cl_sann (&1) (&1),moi_s3cl_sann (&1) (&1)) (tau,tau')
     ==> homeomorphism (moi_s3cl_sann a b,moi_s3cl_sann a b)
                       (moi_s3cl_rad tau,moi_s3cl_rad tau')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tau:real^2->real^2`; `tau':real^2->real^2`; `a:real`; `b:real`]
    MOI_S3CL_RAD_HALF) THEN
  MP_TAC(SPECL [`tau':real^2->real^2`; `tau:real^2->real^2`; `a:real`; `b:real`]
    MOI_S3CL_RAD_HALF) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

let MOI_S3CL_AFF_CONT = prove
 (`!a b c d (s:real^2->bool).
     (lift o (\z:real^2. c + (infnorm z - a) * (d - c) / (b - a))) continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[o_DEF; LIFT_ADD; LIFT_SUB] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(x - a) * y = y * (x - a)`] THEN
  REWRITE_TAC[LIFT_CMUL; LIFT_SUB] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN REWRITE_TAC[GSYM o_DEF; MOI_S3CL_INFNORM_CONT]);;

(* The radial affine map of the annulus a <= infnorm <= b onto c <= infnorm <= d. *)

let MOI_S3CL_SCL_HALF = prove
 (`!a b c d.
     &0 < a /\ a < b /\ &0 < c /\ c < d
     ==> moi_s3cl_scl a b c d continuous_on moi_s3cl_sann a b /\
         IMAGE (moi_s3cl_scl a b c d) (moi_s3cl_sann a b) SUBSET moi_s3cl_sann c d /\
         (!z. z IN moi_s3cl_sann a b
              ==> moi_s3cl_scl c d a b (moi_s3cl_scl a b c d z) = z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN moi_s3cl_sann a b
                    ==> ~(z = vec 0) /\ &0 < infnorm z /\ a <= infnorm z /\ infnorm z <= b /\
                        infnorm(inv(infnorm z) % z) = &1`
  (LABEL_TAC "dir") THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a:real`; `b:real`; `z:real^2`] MOI_S3CL_SANN_NZ) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[MOI_S3CL_DIR_NORM] THEN
    UNDISCH_TAC `(z:real^2) IN moi_s3cl_sann a b` THEN
    REWRITE_TAC[moi_s3cl_sann; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN moi_s3cl_sann a b
                    ==> infnorm(moi_s3cl_scl a b c d z) =
                        c + (infnorm z - a) * (d - c) / (b - a) /\
                        c <= c + (infnorm z - a) * (d - c) / (b - a) /\
                        c + (infnorm z - a) * (d - c) / (b - a) <= d`
  (LABEL_TAC "nrm") THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    USE_THEN "dir" (MP_TAC o C MP (ASSUME `(z:real^2) IN moi_s3cl_sann a b`) o
                    SPEC `z:real^2`) THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= (infnorm(z:real^2) - a) * (d - c) / (b - a) /\
                  (infnorm(z:real^2) - a) * (d - c) / (b - a) <= d - c`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
        ONCE_REWRITE_TAC[REAL_ARITH `(x * y) * z = (x * z) * y`] THEN
        REWRITE_TAC[GSYM real_div] THEN
        MATCH_MP_TAC(REAL_ARITH `x * y <= &1 * y ==> x * y <= y`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    REWRITE_TAC[moi_s3cl_scl] THEN ONCE_REWRITE_TAC[INFNORM_MUL] THEN
    ASM_REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `moi_s3cl_scl a b c d =
      (\z. (c + (infnorm z - a) * (d - c) / (b - a)) % (\z:real^2. inv(infnorm z) % z) z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_s3cl_scl]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[MOI_S3CL_AFF_CONT];
      REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC MOI_S3CL_DIR_CONT THEN
      DISCH_THEN(fun th -> USE_THEN "dir" (MP_TAC o C MP th o SPEC `vec 0:real^2`)) THEN
      REWRITE_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    USE_THEN "nrm" (MP_TAC o C MP (ASSUME `(z:real^2) IN moi_s3cl_sann a b`) o
                    SPEC `z:real^2`) THEN
    REWRITE_TAC[moi_s3cl_sann; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    USE_THEN "dir" (MP_TAC o C MP (ASSUME `(z:real^2) IN moi_s3cl_sann a b`) o
                    SPEC `z:real^2`) THEN STRIP_TAC THEN
    USE_THEN "nrm" (MP_TAC o C MP (ASSUME `(z:real^2) IN moi_s3cl_sann a b`) o
                    SPEC `z:real^2`) THEN STRIP_TAC THEN
    ABBREV_TAC `u = c + (infnorm(z:real^2) - a) * (d - c) / (b - a)` THEN
    SUBGOAL_THEN `&0 < u` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [moi_s3cl_scl] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv u % moi_s3cl_scl a b c d z = inv(infnorm z) % (z:real^2)`
    SUBST1_TAC THENL
     [REWRITE_TAC[moi_s3cl_scl] THEN ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID; REAL_MUL_LID];
      ALL_TAC] THEN
    SUBGOAL_THEN `a + (u - c) * (b - a) / (d - c) = infnorm(z:real^2)` SUBST1_TAC THENL
     [EXPAND_TAC "u" THEN
      SUBGOAL_THEN `~(d - c = &0) /\ ~(b - a = &0)` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `~(d - c = &0)` THEN UNDISCH_TAC `~(b - a = &0)` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]]);;

let MOI_S3CL_SCL_HOMEO = prove
 (`!a b c d.
     &0 < a /\ a < b /\ &0 < c /\ c < d
     ==> homeomorphism (moi_s3cl_sann a b,moi_s3cl_sann c d)
                       (moi_s3cl_scl a b c d,moi_s3cl_scl c d a b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `c:real`; `d:real`] MOI_S3CL_SCL_HALF) THEN
  MP_TAC(SPECL [`c:real`; `d:real`; `a:real`; `b:real`] MOI_S3CL_SCL_HALF) THEN
  ASM_REWRITE_TAC[homeomorphism] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

(* The circles: scl maps a w to c w and b w to d w (infnorm w = 1).         *)

let MOI_S3CL_SCL_CIRCLES = prove
 (`!a b c d w.
     &0 < a /\ a < b /\ infnorm w = &1
     ==> moi_s3cl_scl a b c d (a % w) = c % w /\
         moi_s3cl_scl a b c d (b % w) = d % w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(a = &0) /\ ~(b = &0) /\ ~(b - a = &0) /\ abs a = a /\ abs b = b`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_s3cl_scl; INFNORM_MUL] THEN ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `~(b - a = &0)` THEN UNDISCH_TAC `~(b = &0)` THEN
  UNDISCH_TAC `~(a = &0)` THEN CONV_TAC REAL_FIELD);;

(* The square annulus of pl_annulus_with_ends and its two boundary squares  *)
(* as infnorm annuli (the set forms of MOI_FH1_SQUARE_ANNULUS_INFNORM and    *)
(* MOI_FH1_SQUARE_FRONTIER_INFNORM of pc_moi_fnd_h1, not in this closure).   *)

let MOI_S3CL_SQ = prove
 (`interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
   interval(--vector[&1;&1]:real^2,vector[&1;&1]) = moi_s3cl_sann (&1) (&2)`,
  REWRITE_TAC[EXTENSION; moi_s3cl_sann; IN_ELIM_THM; IN_DIFF; IN_INTERVAL; DIMINDEX_2;
              FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT; INFNORM_2] THEN
  REAL_ARITH_TAC);;

let MOI_S3CL_RF = prove
 (`!c. &0 < c
       ==> relative_frontier(interval[--vector[c;c]:real^2,vector[c;c]]) =
           moi_s3cl_sann c c`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RELATIVE_FRONTIER_NONEMPTY_INTERIOR o
    lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY] THEN
    REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[EXTENSION; moi_s3cl_sann; IN_ELIM_THM; FRONTIER_CLOSED_INTERVAL; IN_DIFF;
              IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT;
              INFNORM_2] THEN
  ASM_REAL_ARITH_TAC);;

(* Scaling the unit infnorm circle onto the circle of radius p.             *)

let MOI_S3CL_SCALE_CIRC = prove
 (`!p. &0 < p
       ==> homeomorphism (moi_s3cl_sann (&1) (&1),moi_s3cl_sann p p)
                         ((\w:real^2. p % w),(\v. inv p % v))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[homeomorphism] THEN
  SUBGOAL_THEN `abs p = p /\ ~(p = &0) /\ abs(inv p) = inv p` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_INV] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_s3cl_sann; IN_ELIM_THM; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_RINV; VECTOR_MUL_LID] THEN
  SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  CONJ_TAC THEN X_GEN_TAC `y:real^2` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `infnorm(x:real^2) = &1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[INFNORM_MUL; REAL_MUL_RID; REAL_LE_REFL]];
    STRIP_TAC THEN EXISTS_TAC `inv p % (y:real^2)` THEN
    SUBGOAL_THEN `infnorm(y:real^2) = p` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; INFNORM_MUL] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LINV; VECTOR_MUL_LID; REAL_LE_REFL];
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `infnorm(x:real^2) = p` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[INFNORM_MUL] THEN ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LE_REFL]];
    STRIP_TAC THEN EXISTS_TAC `p % (y:real^2)` THEN
    SUBGOAL_THEN `infnorm(y:real^2) = &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; INFNORM_MUL; REAL_MUL_RID; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_LID]]);;

(* Two parametrizations of annuli sharing a boundary circle (the circle of  *)
(* radius p of the first, of radius q of the second) induce a homeomorphism *)
(* of the unit infnorm circle.                                               *)

let MOI_S3CL_TRANS = prove
 (`!(f:real^2->real^N) f' f1 f1' a a1 p q.
     &0 < p /\ &0 < q /\
     homeomorphism (moi_s3cl_sann (&1) (&2),a) (f,f') /\
     homeomorphism (moi_s3cl_sann (&1) (&2),a1) (f1,f1') /\
     moi_s3cl_sann p p SUBSET moi_s3cl_sann (&1) (&2) /\
     moi_s3cl_sann q q SUBSET moi_s3cl_sann (&1) (&2) /\
     IMAGE f (moi_s3cl_sann p p) = IMAGE f1 (moi_s3cl_sann q q)
     ==> homeomorphism (moi_s3cl_sann (&1) (&1),moi_s3cl_sann (&1) (&1))
           ((\w. inv q % f1'(f(p % w))),(\y. inv p % f'(f1(q % y))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\w. inv q % (f1':real^N->real^2)((f:real^2->real^N)(p % w))) =
    (\v. inv q % v) o f1' o f o (\w. p % w) /\
    (\y. inv p % (f':real^N->real^2)((f1:real^2->real^N)(q % y))) =
    (((\v. inv p % v) o f') o f1) o (\w. q % w)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `moi_s3cl_sann q q` THEN CONJ_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN MATCH_MP_TAC MOI_S3CL_SCALE_CIRC THEN
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `IMAGE (f1:real^2->real^N) (moi_s3cl_sann q q)` THEN CONJ_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`moi_s3cl_sann (&1) (&2)`; `a1:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `homeomorphism (moi_s3cl_sann (&1) (&2),a1)
                   ((f1:real^2->real^N),(f1':real^N->real^2))` THEN
    REWRITE_TAC[homeomorphism] THEN ASM SET_TAC[]] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    can (find_term ((=) `f1:real^2->real^N`)) (concl th))) THEN
  MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `moi_s3cl_sann p p` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3CL_SCALE_CIRC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`moi_s3cl_sann (&1) (&2)`; `a:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `homeomorphism (moi_s3cl_sann (&1) (&2),a)
                   ((f:real^2->real^N),(f':real^N->real^2))` THEN
    REWRITE_TAC[homeomorphism] THEN ASM SET_TAC[]]);;

(* Forward step: re-parametrize the next annulus so that its inner circle   *)
(* agrees with the outer circle of the previous one: h w = f(2 w).          *)

let MOI_S3CL_STEP_FWD = prove
 (`!(f:real^2->real^N) f' f1 f1' a a1.
     homeomorphism (moi_s3cl_sann (&1) (&2),a) (f,f') /\
     homeomorphism (moi_s3cl_sann (&1) (&2),a1) (f1,f1') /\
     IMAGE f (moi_s3cl_sann (&2) (&2)) = IMAGE f1 (moi_s3cl_sann (&1) (&1))
     ==> ?h h'. homeomorphism (moi_s3cl_sann (&1) (&2),a1) (h,h') /\
                (!w. w IN moi_s3cl_sann (&1) (&1) ==> h w = f (&2 % w)) /\
                IMAGE h (moi_s3cl_sann (&1) (&1)) = IMAGE f1 (moi_s3cl_sann (&1) (&1)) /\
                IMAGE h (moi_s3cl_sann (&2) (&2)) = IMAGE f1 (moi_s3cl_sann (&2) (&2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `f':real^N->real^2`; `f1:real^2->real^N`;
                 `f1':real^N->real^2`; `a:real^N->bool`; `a1:real^N->bool`; `&2`; `&1`]
                MOI_S3CL_TRANS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_s3cl_sann; SUBSET; IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `tau = \w:real^2. inv(&1) % (f1':real^N->real^2)((f:real^2->real^N)(&2 % w))` THEN
  ABBREV_TAC `tau' = \y:real^2. inv(&2) % (f':real^N->real^2)((f1:real^2->real^N)(&1 % y))` THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`(f1:real^2->real^N) o moi_s3cl_rad tau`;
                        `moi_s3cl_rad tau' o (f1':real^N->real^2)`] THEN
  SUBGOAL_THEN `!c. &0 < c
                    ==> IMAGE (moi_s3cl_rad tau) (moi_s3cl_sann c c) = moi_s3cl_sann c c`
  (LABEL_TAC "im") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tau:real^2->real^2`; `tau':real^2->real^2`; `c:real`; `c:real`]
                  MOI_S3CL_RAD_HOMEO) THEN
    ASM_SIMP_TAC[homeomorphism];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN USE_THEN "im" (fun th -> SIMP_TAC[th; REAL_LT_01; REAL_ARITH `&0 < &2`]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `moi_s3cl_sann (&1) (&2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3CL_RAD_HOMEO THEN ASM_REWRITE_TAC[REAL_LT_01];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `infnorm(w:real^2) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^2) IN moi_s3cl_sann (&1) (&1)` THEN
    REWRITE_TAC[moi_s3cl_sann; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[o_THM; moi_s3cl_rad; REAL_INV_1; VECTOR_MUL_LID] THEN
  EXPAND_TAC "tau" THEN REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID] THEN
  SUBGOAL_THEN `(f:real^2->real^N) (&2 % w) IN IMAGE f1 (moi_s3cl_sann (&1) (&1))`
  MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `f1:real^2->real^N`)) (lhs(concl th) ) = false &&
      can (find_term ((=) `f1:real^2->real^N`)) (rand(concl th)) &&
      can (find_term ((=) `f:real^2->real^N`)) (lhs(concl th)))) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[moi_s3cl_sann; IN_ELIM_THM; INFNORM_MUL] THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `homeomorphism (moi_s3cl_sann (&1) (&2),a1)
                 ((f1:real^2->real^N),(f1':real^N->real^2))` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s3cl_sann (&1) (&1) SUBSET moi_s3cl_sann (&1) (&2)` MP_TAC THENL
   [REWRITE_TAC[moi_s3cl_sann; SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM SET_TAC[]);;

(* Backward step: re-parametrize the previous annulus so that its outer     *)
(* circle agrees with the inner circle of the next one: h(2 w) = f w.      *)

let MOI_S3CL_STEP_BWD = prove
 (`!(f:real^2->real^N) f' f0 f0' a a0.
     homeomorphism (moi_s3cl_sann (&1) (&2),a) (f,f') /\
     homeomorphism (moi_s3cl_sann (&1) (&2),a0) (f0,f0') /\
     IMAGE f (moi_s3cl_sann (&1) (&1)) = IMAGE f0 (moi_s3cl_sann (&2) (&2))
     ==> ?h h'. homeomorphism (moi_s3cl_sann (&1) (&2),a0) (h,h') /\
                (!w. w IN moi_s3cl_sann (&1) (&1) ==> h (&2 % w) = f w) /\
                IMAGE h (moi_s3cl_sann (&1) (&1)) = IMAGE f0 (moi_s3cl_sann (&1) (&1)) /\
                IMAGE h (moi_s3cl_sann (&2) (&2)) = IMAGE f0 (moi_s3cl_sann (&2) (&2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `f':real^N->real^2`; `f0:real^2->real^N`;
                 `f0':real^N->real^2`; `a:real^N->bool`; `a0:real^N->bool`; `&1`; `&2`]
                MOI_S3CL_TRANS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_s3cl_sann; SUBSET; IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `sg = \w:real^2. inv(&2) % (f0':real^N->real^2)((f:real^2->real^N)(&1 % w))` THEN
  ABBREV_TAC `sg' = \y:real^2. inv(&1) % (f':real^N->real^2)((f0:real^2->real^N)(&2 % y))` THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`(f0:real^2->real^N) o moi_s3cl_rad sg`;
                        `moi_s3cl_rad sg' o (f0':real^N->real^2)`] THEN
  SUBGOAL_THEN `!c. &0 < c
                    ==> IMAGE (moi_s3cl_rad sg) (moi_s3cl_sann c c) = moi_s3cl_sann c c`
  (LABEL_TAC "im") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`sg:real^2->real^2`; `sg':real^2->real^2`; `c:real`; `c:real`]
                  MOI_S3CL_RAD_HOMEO) THEN
    ASM_SIMP_TAC[homeomorphism];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN USE_THEN "im" (fun th -> SIMP_TAC[th; REAL_LT_01; REAL_ARITH `&0 < &2`]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `moi_s3cl_sann (&1) (&2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3CL_RAD_HOMEO THEN ASM_REWRITE_TAC[REAL_LT_01];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `infnorm(w:real^2) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^2) IN moi_s3cl_sann (&1) (&1)` THEN
    REWRITE_TAC[moi_s3cl_sann; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[o_THM; moi_s3cl_rad; INFNORM_MUL] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `abs(&2) * &1 = &2`; VECTOR_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[VECTOR_MUL_LID] THEN
  EXPAND_TAC "sg" THEN REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_LID] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[VECTOR_MUL_LID] THEN
  SUBGOAL_THEN `(f:real^2->real^N) w IN IMAGE f0 (moi_s3cl_sann (&2) (&2))`
  MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `f0:real^2->real^N`)) (rand(concl th)) &&
      can (find_term ((=) `f:real^2->real^N`)) (lhs(concl th)))) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `homeomorphism (moi_s3cl_sann (&1) (&2),a0)
                 ((f0:real^2->real^N),(f0':real^N->real^2))` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s3cl_sann (&2) (&2) SUBSET moi_s3cl_sann (&1) (&2)` MP_TAC THENL
   [REWRITE_TAC[moi_s3cl_sann; SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM SET_TAC[]);;


(* ========================================================================= *)
(* Part 2: compatible parametrizations of a bi-infinite chain of            *)
(* annuli (MOI_S3CL_CHAIN_PARAM).                                            *)
(* ========================================================================= *)

(* A bi-infinite chain of annuli aa k with circles cc k, cc (k + 1) has      *)
(* parametrizations by the square annulus agreeing on the shared circles:  *)
(* psi k (2 w) = psi (k + 1) w (forward and backward recursion from 0).     *)

let MOI_S3CL_CHAIN_FWD = prove
 (`!(aa:int->real^N->bool) cc phi phi'.
     (!k. homeomorphism (moi_s3cl_sann (&1) (&2),aa k) (phi k,phi' k) /\
          IMAGE (phi k) (moi_s3cl_sann (&1) (&1)) = cc k /\
          IMAGE (phi k) (moi_s3cl_sann (&2) (&2)) = cc (k + &1))
     ==> ?fw:num->(real^2->real^N)#(real^N->real^2).
           fw 0 = (phi(&0),phi'(&0)) /\
           (!n. homeomorphism (moi_s3cl_sann (&1) (&2),aa(&n)) (FST(fw n),SND(fw n)) /\
                IMAGE (FST(fw n)) (moi_s3cl_sann (&1) (&1)) = cc(&n) /\
                IMAGE (FST(fw n)) (moi_s3cl_sann (&2) (&2)) = cc(&n + &1)) /\
           (!n w. w IN moi_s3cl_sann (&1) (&1)
                  ==> FST(fw(SUC n)) w = FST(fw n) (&2 % w))`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "phi") THEN
  MP_TAC(ISPECL
   [`\n:num z:(real^2->real^N)#(real^N->real^2).
       homeomorphism (moi_s3cl_sann (&1) (&2),(aa:int->real^N->bool)(&n)) (FST z,SND z) /\
       IMAGE (FST z) (moi_s3cl_sann (&1) (&1)) = (cc:int->real^N->bool)(&n) /\
       IMAGE (FST z) (moi_s3cl_sann (&2) (&2)) = cc(&n + &1)`;
    `\n:num z:(real^2->real^N)#(real^N->real^2) z':(real^2->real^N)#(real^N->real^2).
       !w. w IN moi_s3cl_sann (&1) (&1) ==> FST z' w = FST z (&2 % w)`;
    `(phi:int->real^2->real^N) (&0),(phi':int->real^N->real^2) (&0)`]
   DEPENDENT_CHOICE_FIXED) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[FST; SND]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:(real^2->real^N)#(real^N->real^2)`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`FST(z:(real^2->real^N)#(real^N->real^2))`;
                   `SND(z:(real^2->real^N)#(real^N->real^2))`;
                   `(phi:int->real^2->real^N)(&(SUC n))`;
                   `(phi':int->real^N->real^2)(&(SUC n))`;
                   `(aa:int->real^N->bool)(&n)`; `(aa:int->real^N->bool)(&(SUC n))`]
                  MOI_S3CL_STEP_FWD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN
      USE_THEN "phi" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^N` (X_CHOOSE_THEN `h':real^N->real^2`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `(h:real^2->real^N),(h':real^N->real^2)` THEN
    ASM_REWRITE_TAC[FST; SND] THEN REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN
    USE_THEN "phi" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]);;

let MOI_S3CL_CHAIN_BWD = prove
 (`!(aa:int->real^N->bool) cc phi phi'.
     (!k. homeomorphism (moi_s3cl_sann (&1) (&2),aa k) (phi k,phi' k) /\
          IMAGE (phi k) (moi_s3cl_sann (&1) (&1)) = cc k /\
          IMAGE (phi k) (moi_s3cl_sann (&2) (&2)) = cc (k + &1))
     ==> ?bw:num->(real^2->real^N)#(real^N->real^2).
           bw 0 = (phi(&0),phi'(&0)) /\
           (!n. homeomorphism (moi_s3cl_sann (&1) (&2),aa(--(&n))) (FST(bw n),SND(bw n)) /\
                IMAGE (FST(bw n)) (moi_s3cl_sann (&1) (&1)) = cc(--(&n)) /\
                IMAGE (FST(bw n)) (moi_s3cl_sann (&2) (&2)) = cc(--(&n) + &1)) /\
           (!n w. w IN moi_s3cl_sann (&1) (&1)
                  ==> FST(bw(SUC n)) (&2 % w) = FST(bw n) w)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "phi") THEN
  MP_TAC(ISPECL
   [`\n:num z:(real^2->real^N)#(real^N->real^2).
       homeomorphism (moi_s3cl_sann (&1) (&2),(aa:int->real^N->bool)(--(&n))) (FST z,SND z) /\
       IMAGE (FST z) (moi_s3cl_sann (&1) (&1)) = (cc:int->real^N->bool)(--(&n)) /\
       IMAGE (FST z) (moi_s3cl_sann (&2) (&2)) = cc(--(&n) + &1)`;
    `\n:num z:(real^2->real^N)#(real^N->real^2) z':(real^2->real^N)#(real^N->real^2).
       !w. w IN moi_s3cl_sann (&1) (&1) ==> FST z' (&2 % w) = FST z w`;
    `(phi:int->real^2->real^N) (&0),(phi':int->real^N->real^2) (&0)`]
   DEPENDENT_CHOICE_FIXED) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[FST; SND; INT_NEG_0]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:(real^2->real^N)#(real^N->real^2)`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`FST(z:(real^2->real^N)#(real^N->real^2))`;
                   `SND(z:(real^2->real^N)#(real^N->real^2))`;
                   `(phi:int->real^2->real^N)(--(&(SUC n)))`;
                   `(phi':int->real^N->real^2)(--(&(SUC n)))`;
                   `(aa:int->real^N->bool)(--(&n))`; `(aa:int->real^N->bool)(--(&(SUC n)))`]
                  MOI_S3CL_STEP_BWD) THEN
    SUBGOAL_THEN `--(&(SUC n)) + &1:int = --(&n)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN INT_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "phi" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^N` (X_CHOOSE_THEN `h':real^N->real^2`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `(h:real^2->real^N),(h':real^N->real^2)` THEN
    ASM_REWRITE_TAC[FST; SND] THEN USE_THEN "phi" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]);;

(* The case k = &n of MOI_S3CL_CHAIN_PARAM (also used for k = --(&0)).      *)

let MOI_S3CL_POS_TAC n =
  REWRITE_TAC[INT_POS; NUM_OF_INT_OF_NUM; GSYM INT_OF_NUM_SUC] THEN
  REWRITE_TAC[INT_OF_NUM_SUC; INT_ARITH `!n. &0:int <= &n + &1`] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_SUC; NUM_OF_INT_OF_NUM] THEN
  USE_THEN "fwP" (MP_TAC o SPEC n) THEN REWRITE_TAC[INT_OF_NUM_SUC; PAIR] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "fwR" (fun th -> SIMP_TAC[th]);;

let MOI_S3CL_CHAIN_PARAM = prove
 (`!(aa:int->real^N->bool) cc.
     (!k. ?f f'. homeomorphism (moi_s3cl_sann (&1) (&2),aa k) (f,f') /\
                 IMAGE f (moi_s3cl_sann (&1) (&1)) = cc k /\
                 IMAGE f (moi_s3cl_sann (&2) (&2)) = cc (k + &1))
     ==> ?psi psi'.
           !k. homeomorphism (moi_s3cl_sann (&1) (&2),aa k) (psi k,psi' k) /\
               IMAGE (psi k) (moi_s3cl_sann (&1) (&1)) = cc k /\
               IMAGE (psi k) (moi_s3cl_sann (&2) (&2)) = cc (k + &1) /\
               (!w. w IN moi_s3cl_sann (&1) (&1) ==> psi k (&2 % w) = psi (k + &1) w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:int->real^2->real^N`
    (X_CHOOSE_THEN `phi':int->real^N->real^2` (LABEL_TAC "phi"))) THEN
  MP_TAC(ISPECL [`aa:int->real^N->bool`; `cc:int->real^N->bool`;
                 `phi:int->real^2->real^N`; `phi':int->real^N->real^2`] MOI_S3CL_CHAIN_FWD) THEN
  ANTS_TAC THENL [USE_THEN "phi" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `fw:num->(real^2->real^N)#(real^N->real^2)`
    (CONJUNCTS_THEN2 (LABEL_TAC "fw0") (CONJUNCTS_THEN2 (LABEL_TAC "fwP") (LABEL_TAC "fwR")))) THEN
  MP_TAC(ISPECL [`aa:int->real^N->bool`; `cc:int->real^N->bool`;
                 `phi:int->real^2->real^N`; `phi':int->real^N->real^2`] MOI_S3CL_CHAIN_BWD) THEN
  ANTS_TAC THENL [USE_THEN "phi" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `bw:num->(real^2->real^N)#(real^N->real^2)`
    (CONJUNCTS_THEN2 (LABEL_TAC "bw0") (CONJUNCTS_THEN2 (LABEL_TAC "bwP") (LABEL_TAC "bwR")))) THEN
  SUBGOAL_THEN `FST((bw:num->(real^2->real^N)#(real^N->real^2)) 0) =
                FST((fw:num->(real^2->real^N)#(real^N->real^2)) 0)`
  (LABEL_TAC "eq0") THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\k:int. if &0 <= k then FST((fw:num->(real^2->real^N)#(real^N->real^2)) (num_of_int k))
             else FST((bw:num->(real^2->real^N)#(real^N->real^2)) (num_of_int(--k)))`;
    `\k:int. if &0 <= k then SND((fw:num->(real^2->real^N)#(real^N->real^2)) (num_of_int k))
             else SND((bw:num->(real^2->real^N)#(real^N->real^2)) (num_of_int(--k)))`] THEN
  X_GEN_TAC `k:int` THEN REWRITE_TAC[] THEN
  DISJ_CASES_THEN (X_CHOOSE_THEN `n:num` SUBST1_TAC) (SPEC `k:int` INT_IMAGE) THENL
   [MOI_S3CL_POS_TAC `n:num`; ALL_TAC] THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `m:num` SUBST1_TAC) (SPEC `n:num` num_CASES)
  THENL [REWRITE_TAC[INT_NEG_0] THEN MOI_S3CL_POS_TAC `0`; ALL_TAC] THEN
  SUBGOAL_THEN `~(&0:int <= --(&(SUC m)))` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INT_NEG_NEG; NUM_OF_INT_OF_NUM] THEN
  SUBGOAL_THEN `--(&(SUC m)) + &1:int = --(&m)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN INT_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "bwP" (MP_TAC o SPEC `SUC m`) THEN
  SUBGOAL_THEN `--(&(SUC m)) + &1:int = --(&m)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[PAIR] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
  USE_THEN "bwR" (MP_TAC o C MP (ASSUME `(w:real^2) IN moi_s3cl_sann (&1) (&1)`) o
                  SPECL [`m:num`; `w:real^2`]) THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[INT_NEG_0; INT_POS; NUM_OF_INT_OF_NUM] THEN
    USE_THEN "eq0" (fun th -> REWRITE_TAC[th]);
    SUBGOAL_THEN `~(&0:int <= --(&m))` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `~(m = 0)` THEN REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC;
      REWRITE_TAC[INT_NEG_NEG; NUM_OF_INT_OF_NUM]]]);;


(* ========================================================================= *)
(* Part 3: the model radii al k in (0,1), the pasting lemma for             *)
(* locally finite closed covers in Euclidean spaces, and the two glued maps *)
(* fz (open unit square to the chain) and gx (back) with their piece        *)
(* formulas.                                                                 *)
(* ========================================================================= *)

let moi_s3cl_lev = new_definition
 `moi_s3cl_lev (x:real) = (&1 + x / (&1 + abs x)) / &2`;;

let moi_s3cl_al = new_definition
 `moi_s3cl_al (k:int) = moi_s3cl_lev (real_of_int k)`;;

(* The model radii al k in (0,1), strictly increasing, tending to 0.        *)

let MOI_S3CL_LEV_BOUNDS = prove
 (`!x. &0 < moi_s3cl_lev x /\ moi_s3cl_lev x < &1`,
  GEN_TAC THEN REWRITE_TAC[moi_s3cl_lev] THEN
  SUBGOAL_THEN `abs(x / (&1 + abs x)) < &1` MP_TAC THENL
   [REWRITE_TAC[REAL_ABS_DIV] THEN
    SUBGOAL_THEN `abs(&1 + abs x) = &1 + abs x /\ &0 < &1 + abs x` STRIP_ASSUME_TAC THENL
     [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

let MOI_S3CL_LEV_MONO = prove
 (`!x y. x < y ==> moi_s3cl_lev x < moi_s3cl_lev y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s3cl_lev] THEN
  MATCH_MP_TAC(REAL_ARITH `u < v ==> (&1 + u) / &2 < (&1 + v) / &2`) THEN
  SUBGOAL_THEN `&0 < &1 + abs x /\ &0 < &1 + abs y` STRIP_ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a / b * c = (a * c) / b`] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
  ASM_CASES_TAC `&0 <= x` THENL
   [SUBGOAL_THEN `abs x = x /\ abs y = y` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= y` THENL
   [SUBGOAL_THEN `abs x = --x /\ abs y = y` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= --x * y` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `abs x = --x /\ abs y = --y` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

let MOI_S3CL_LEV_ONTO = prove
 (`!s. &0 < s /\ s < &1 ==> ?x. moi_s3cl_lev x = s`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(&2 * s - &1) / (&1 - abs(&2 * s - &1))` THEN
  REWRITE_TAC[moi_s3cl_lev] THEN
  SUBGOAL_THEN `&0 < &1 - abs(&2 * s - &1)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs((&2 * s - &1) / (&1 - abs(&2 * s - &1))) =
                abs(&2 * s - &1) / (&1 - abs(&2 * s - &1))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_DIV] THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 < &1 - abs(&2 * s - &1)` THEN CONV_TAC REAL_FIELD);;

let MOI_S3CL_AL_BOUNDS = prove
 (`!k. &0 < moi_s3cl_al k /\ moi_s3cl_al k < &1`,
  REWRITE_TAC[moi_s3cl_al; MOI_S3CL_LEV_BOUNDS]);;

let MOI_S3CL_AL_MONO = prove
 (`!m n. m < n ==> moi_s3cl_al m < moi_s3cl_al n`,
  REWRITE_TAC[moi_s3cl_al; int_lt; MOI_S3CL_LEV_MONO]);;

let MOI_S3CL_AL_LT = prove
 (`!m n. moi_s3cl_al m < moi_s3cl_al n <=> m < n`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[MOI_S3CL_AL_MONO] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[INT_NOT_LT; REAL_NOT_LT] THEN
  REWRITE_TAC[INT_LE_LT] THEN STRIP_TAC THEN ASM_SIMP_TAC[MOI_S3CL_AL_MONO; REAL_LT_IMP_LE] THEN
  REAL_ARITH_TAC);;

let MOI_S3CL_AL_LE = prove
 (`!m n. moi_s3cl_al m <= moi_s3cl_al n <=> m <= n`,
  REWRITE_TAC[GSYM REAL_NOT_LT; GSYM INT_NOT_LT; MOI_S3CL_AL_LT]);;

let MOI_S3CL_AL_INT = prove
 (`!s. &0 < s /\ s < &1
       ==> ?k. moi_s3cl_al k <= s /\ s < moi_s3cl_al (k + &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `s:real` MOI_S3CL_LEV_ONTO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` (SUBST1_TAC o SYM)) THEN
  EXISTS_TAC `int_of_real(floor x)` THEN
  REWRITE_TAC[moi_s3cl_al; int_add_th; int_of_num_th] THEN
  MP_TAC(SPEC `x:real` FLOOR) THEN STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_OF_INT_OF_REAL] THEN CONJ_TAC THENL
   [ASM_CASES_TAC `floor x = x` THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC MOI_S3CL_LEV_MONO THEN
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC MOI_S3CL_LEV_MONO THEN ASM_REWRITE_TAC[]]);;

let MOI_S3CL_AL_LOW = prove
 (`!e. &0 < e ==> ?k. moi_s3cl_al k < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `inv e` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  EXISTS_TAC `--(&n):int` THEN
  REWRITE_TAC[moi_s3cl_al; moi_s3cl_lev; int_neg_th; int_of_num_th] THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM] THEN
  SUBGOAL_THEN `&0 < &1 + &n` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + --(&n) / (&1 + &n)) / &2 = inv(&2 * (&1 + &n))` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < &1 + &n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_LINV THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&n` THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* PASTING_LEMMA_LOCALLY_FINITE for maps between Euclidean spaces.         *)

let MOI_S3CL_PASTE = prove
 (`!(f:K->real^M->real^N) g t k s.
     (!x. x IN s ==> ?u. open u /\ x IN u /\ FINITE {i | i IN k /\ ~(t i INTER u = {})}) /\
     (!i. i IN k ==> closed_in (subtopology euclidean s) (t i) /\ f i continuous_on t i) /\
     (!i j x. i IN k /\ j IN k /\ x IN s INTER t i INTER t j ==> f i x = f j x) /\
     (!x. x IN s ==> ?j. j IN k /\ x IN t j /\ g x = f j x)
     ==> g continuous_on s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN] THEN
  MATCH_MP_TAC PASTING_LEMMA_LOCALLY_FINITE THEN
  MAP_EVERY EXISTS_TAC [`f:K->real^M->real^N`; `t:K->real^M->bool`; `k:K->bool`] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC o
      C MATCH_MP (ASSUME `(x:real^M) IN s`) o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "FINITE")) (concl th))) THEN
    EXISTS_TAC `s INTER u:real^M->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; IN_INTER] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{i | i IN k /\ ~((t:K->real^M->bool) i INTER u = {})}` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(i:K) IN k`) o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "closed_in")) (concl th))) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP (SET_RULE `!s t:real^M->bool. t SUBSET s ==> s INTER t = t`) th]) THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN]]);;

let moi_s3cl_kz = new_definition
 `moi_s3cl_kz (z:real^2) =
    @k. moi_s3cl_al k <= infnorm z /\ infnorm z < moi_s3cl_al (k + &1)`;;

let moi_s3cl_fz = new_definition
 `moi_s3cl_fz (psi:int->real^2->real^N) (c0:real^N) (z:real^2) =
    if z = vec 0 then c0
    else psi (moi_s3cl_kz z)
             (moi_s3cl_scl (moi_s3cl_al (moi_s3cl_kz z)) (moi_s3cl_al (moi_s3cl_kz z + &1))
                           (&1) (&2) z)`;;

let moi_s3cl_kx = new_definition
 `moi_s3cl_kx (aa:int->real^N->bool) (x:real^N) = @k. x IN aa k`;;

let moi_s3cl_gx = new_definition
 `moi_s3cl_gx (aa:int->real^N->bool) (psi':int->real^N->real^2) (c0:real^N) (x:real^N) =
    if x = c0 then vec 0
    else moi_s3cl_scl (&1) (&2) (moi_s3cl_al (moi_s3cl_kx aa x))
                      (moi_s3cl_al (moi_s3cl_kx aa x + &1)) (psi' (moi_s3cl_kx aa x) x)`;;

let MOI_S3CL_KZ = prove
 (`!z:real^2. &0 < infnorm z /\ infnorm z < &1
              ==> moi_s3cl_al (moi_s3cl_kz z) <= infnorm z /\
                  infnorm z < moi_s3cl_al (moi_s3cl_kz z + &1)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_s3cl_kz] THEN CONV_TAC SELECT_CONV THEN
  MATCH_MP_TAC MOI_S3CL_AL_INT THEN ASM_REWRITE_TAC[]);;

let MOI_S3CL_AL_UNIQUE = prove
 (`!k k' s. moi_s3cl_al k <= s /\ s < moi_s3cl_al (k + &1) /\
            moi_s3cl_al k' <= s /\ s < moi_s3cl_al (k' + &1)
            ==> k = k'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_s3cl_al k < moi_s3cl_al (k' + &1) /\
                moi_s3cl_al k' < moi_s3cl_al (k + &1)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; REWRITE_TAC[MOI_S3CL_AL_LT] THEN INT_ARITH_TAC]);;

let MOI_S3CL_KZ_UNIQUE = prove
 (`!k z:real^2. moi_s3cl_al k <= infnorm z /\ infnorm z < moi_s3cl_al (k + &1)
                ==> moi_s3cl_kz z = k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3CL_AL_UNIQUE THEN
  EXISTS_TAC `infnorm(z:real^2)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S3CL_KZ THEN
  MP_TAC(SPEC `k:int` MOI_S3CL_AL_BOUNDS) THEN
  MP_TAC(SPEC `k + &1:int` MOI_S3CL_AL_BOUNDS) THEN ASM_REAL_ARITH_TAC);;

(* The piece formula of fz on the model annulus of index k.                 *)

let MOI_S3CL_FZ_PIECE = prove
 (`!(psi:int->real^2->real^N) c0 k z.
     (!k w. w IN moi_s3cl_sann (&1) (&1) ==> psi k (&2 % w) = psi (k + &1) w) /\
     z IN moi_s3cl_sann (moi_s3cl_al k) (moi_s3cl_al (k + &1))
     ==> moi_s3cl_fz psi c0 z =
         psi k (moi_s3cl_scl (moi_s3cl_al k) (moi_s3cl_al (k + &1)) (&1) (&2) z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3cl_sann; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(SPEC `k:int` MOI_S3CL_AL_BOUNDS) THEN
  MP_TAC(SPEC `k + &1:int` MOI_S3CL_AL_BOUNDS) THEN
  MP_TAC(SPEC `k + &2:int` MOI_S3CL_AL_BOUNDS) THEN
  MP_TAC(SPECL [`k:int`; `k + &1:int`] MOI_S3CL_AL_MONO) THEN
  MP_TAC(SPECL [`k + &1:int`; `k + &2:int`] MOI_S3CL_AL_MONO) THEN
  REWRITE_TAC[INT_ARITH `k:int < k + &1 /\ k + &1 < k + &2`] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(z:real^2 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `moi_s3cl_al k <= infnorm(vec 0:real^2)` THEN
    REWRITE_TAC[INFNORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_s3cl_fz] THEN
  ASM_CASES_TAC `infnorm(z:real^2) < moi_s3cl_al (k + &1)` THENL
   [SUBGOAL_THEN `moi_s3cl_kz (z:real^2) = k` (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MOI_S3CL_KZ_UNIQUE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `infnorm(z:real^2) = moi_s3cl_al (k + &1)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s3cl_kz (z:real^2) = k + &1` SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_S3CL_KZ_UNIQUE THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REWRITE_TAC[INT_ARITH `(k + &1) + &1:int = k + &2`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < infnorm(z:real^2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[INFNORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?w:real^2. infnorm w = &1 /\ z = moi_s3cl_al (k + &1) % w`
  (X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `inv(infnorm z) % (z:real^2)` THEN ASM_SIMP_TAC[MOI_S3CL_DIR_NORM] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM(ASSUME `infnorm(z:real^2) = moi_s3cl_al (k + &1)`)] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  FIRST_X_ASSUM((fun th -> ONCE_REWRITE_TAC[th]) o check (fun th ->
    concl th = `z = moi_s3cl_al (k + &1) % (w:real^2)`)) THEN
  MP_TAC(ISPECL [`moi_s3cl_al k`; `moi_s3cl_al (k + &1)`; `&1`; `&2`; `w:real^2`]
    MOI_S3CL_SCL_CIRCLES) THEN
  MP_TAC(ISPECL [`moi_s3cl_al (k + &1)`; `moi_s3cl_al (k + &2)`; `&1`; `&2`; `w:real^2`]
    MOI_S3CL_SCL_CIRCLES) THEN
  ASM_REWRITE_TAC[INT_ARITH `(k + &1) + &1:int = k + &2`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[moi_s3cl_sann; IN_ELIM_THM; REAL_LE_REFL]);;

(* On a shared circle the two model formulas of gx agree.                   *)

let MOI_S3CL_GX_ADJ = prove
 (`!(aa:int->real^N->bool) cc psi psi' k x.
     (!k. homeomorphism (moi_s3cl_sann (&1) (&2),aa k) (psi k,psi' k) /\
          IMAGE (psi k) (moi_s3cl_sann (&1) (&1)) = cc k /\
          IMAGE (psi k) (moi_s3cl_sann (&2) (&2)) = cc (k + &1) /\
          (!w. w IN moi_s3cl_sann (&1) (&1) ==> psi k (&2 % w) = psi (k + &1) w)) /\
     (!k. aa k INTER aa (k + &1) = cc (k + &1)) /\
     x IN aa k /\ x IN aa (k + &1)
     ==> moi_s3cl_scl (&1) (&2) (moi_s3cl_al k) (moi_s3cl_al (k + &1)) (psi' k x) =
         moi_s3cl_scl (&1) (&2) (moi_s3cl_al (k + &1)) (moi_s3cl_al (k + &1 + &1))
                      (psi' (k + &1) x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ps")
    (CONJUNCTS_THEN2 (LABEL_TAC "int") STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:real^N) IN (cc:int->real^N->bool) (k + &1)` MP_TAC THENL
   [USE_THEN "int" (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  USE_THEN "ps" (MP_TAC o SPEC `k + &1:int`) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT1(CONJUNCT2 th))] THEN
    STRIP_ASSUME_TAC th) THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
  USE_THEN "ps" (STRIP_ASSUME_TAC o SPEC `k:int`) THEN
  SUBGOAL_THEN `infnorm(w:real^2) = &1 /\ w IN moi_s3cl_sann (&1) (&2) /\
                &2 % w IN moi_s3cl_sann (&1) (&2)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^2) IN moi_s3cl_sann (&1) (&1)` THEN
    REWRITE_TAC[moi_s3cl_sann; IN_ELIM_THM; INFNORM_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi':int->real^N->real^2) (k + &1) x = w /\ psi' k x = &2 % w`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL
     [USE_THEN "ps" (MP_TAC o CONJUNCT1 o SPEC `k + &1:int`) THEN
      REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
      SUBGOAL_THEN `x = (psi:int->real^2->real^N) k (&2 % w)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      USE_THEN "ps" (MP_TAC o CONJUNCT1 o SPEC `k:int`) THEN
      REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`&1`; `&2`; `moi_s3cl_al k`; `moi_s3cl_al (k + &1)`; `w:real^2`]
    MOI_S3CL_SCL_CIRCLES) THEN
  MP_TAC(ISPECL [`&1`; `&2`; `moi_s3cl_al (k + &1)`; `moi_s3cl_al (k + &1 + &1)`; `w:real^2`]
    MOI_S3CL_SCL_CIRCLES) THEN
  ASM_REWRITE_TAC[REAL_LT_01; REAL_ARITH `&1 < &2`; VECTOR_MUL_LID] THEN
  SIMP_TAC[]);;

let MOI_S3CL_GX_PIECE = prove
 (`!(aa:int->real^N->bool) cc psi psi' c0 k x.
     (!k. homeomorphism (moi_s3cl_sann (&1) (&2),aa k) (psi k,psi' k) /\
          IMAGE (psi k) (moi_s3cl_sann (&1) (&1)) = cc k /\
          IMAGE (psi k) (moi_s3cl_sann (&2) (&2)) = cc (k + &1) /\
          (!w. w IN moi_s3cl_sann (&1) (&1) ==> psi k (&2 % w) = psi (k + &1) w)) /\
     (!k. aa k INTER aa (k + &1) = cc (k + &1)) /\
     (!k m. k + &2 <= m ==> DISJOINT (aa k) (aa m)) /\
     (!k. ~(c0 IN aa k)) /\
     x IN aa k
     ==> moi_s3cl_gx aa psi' c0 x =
         moi_s3cl_scl (&1) (&2) (moi_s3cl_al k) (moi_s3cl_al (k + &1)) (psi' k x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ps")
    (CONJUNCTS_THEN2 (LABEL_TAC "int") (CONJUNCTS_THEN2 (LABEL_TAC "dis")
    (CONJUNCTS_THEN2 (LABEL_TAC "c0") ASSUME_TAC)))) THEN
  SUBGOAL_THEN `~(x:real^N = c0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_s3cl_gx] THEN
  ABBREV_TAC `j = moi_s3cl_kx (aa:int->real^N->bool) x` THEN
  SUBGOAL_THEN `(x:real^N) IN aa (j:int)` ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN REWRITE_TAC[moi_s3cl_kx] THEN CONV_TAC SELECT_CONV THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `j:int = k \/ j = k + &1 \/ k = j + &1` MP_TAC THENL
   [MATCH_MP_TAC(INT_ARITH `~(k + &2 <= j) /\ ~(j + &2 <= k:int)
                            ==> j = k \/ j = k + &1 \/ k = j + &1`) THEN
    CONJ_TAC THEN DISCH_THEN(fun th -> USE_THEN "dis" (MP_TAC o C MATCH_MP th)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM(INT_ARITH `k + &1 + &1:int = (k + &1) + &1`)] THEN
    MATCH_MP_TAC MOI_S3CL_GX_ADJ THEN
    MAP_EVERY EXISTS_TAC [`aa:int->real^N->bool`; `cc:int->real^N->bool`;
                          `psi:int->real^2->real^N`] THEN
    CONJ_TAC THENL [USE_THEN "ps" ACCEPT_TAC; ASM_REWRITE_TAC[]];
    REWRITE_TAC[INT_ARITH `(j + &1) + &1:int = j + &1 + &1`] THEN
    MATCH_MP_TAC MOI_S3CL_GX_ADJ THEN
    MAP_EVERY EXISTS_TAC [`aa:int->real^N->bool`; `cc:int->real^N->bool`;
                          `psi:int->real^2->real^N`] THEN
    CONJ_TAC THENL [USE_THEN "ps" ACCEPT_TAC; ASM_REWRITE_TAC[]]]);;


(* ========================================================================= *)
(* Part 4: the glued homeomorphism.  Model annuli, inverse identities,      *)
(* continuity of both maps (pasting over the locally finite pieces off the  *)
(* centre, and the two ends at the centre), MOI_S3CL_GLUE and                *)
(* MOI_S3CL_CHAIN_DISK: a bi-infinite chain of annuli plus its limit point  *)
(* is an open disk.                                                          *)
(* ========================================================================= *)

(* The model annuli and the scaling homeomorphisms onto the square annulus. *)

let MOI_S3CL_AL_FACTS = prove
 (`!k. &0 < moi_s3cl_al k /\ moi_s3cl_al k < moi_s3cl_al (k + &1) /\
       moi_s3cl_al (k + &1) < &1`,
  GEN_TAC THEN REWRITE_TAC[MOI_S3CL_AL_BOUNDS; MOI_S3CL_AL_LT] THEN INT_ARITH_TAC);;

let MOI_S3CL_MODEL_SCL = prove
 (`!k. homeomorphism (moi_s3cl_sann (moi_s3cl_al k) (moi_s3cl_al (k + &1)),
                      moi_s3cl_sann (&1) (&2))
         (moi_s3cl_scl (moi_s3cl_al k) (moi_s3cl_al (k + &1)) (&1) (&2),
          moi_s3cl_scl (&1) (&2) (moi_s3cl_al k) (moi_s3cl_al (k + &1)))`,
  GEN_TAC THEN MATCH_MP_TAC MOI_S3CL_SCL_HOMEO THEN
  REWRITE_TAC[MOI_S3CL_AL_FACTS] THEN REAL_ARITH_TAC);;

let MOI_S3CL_MODEL_IN = prove
 (`!k z. z IN moi_s3cl_sann (moi_s3cl_al k) (moi_s3cl_al (k + &1))
         ==> infnorm z < &1 /\ ~(z = vec 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3cl_sann; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(SPEC `k:int` MOI_S3CL_AL_FACTS) THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `moi_s3cl_al k <= infnorm(vec 0:real^2)` THEN
    REWRITE_TAC[INFNORM_0] THEN ASM_REAL_ARITH_TAC]);;

let MOI_S3CL_MODEL_KZ = prove
 (`!z:real^2. infnorm z < &1 /\ ~(z = vec 0)
              ==> z IN moi_s3cl_sann (moi_s3cl_al (moi_s3cl_kz z))
                                      (moi_s3cl_al (moi_s3cl_kz z + &1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s3cl_sann; IN_ELIM_THM] THEN
  MP_TAC(SPEC `z:real^2` MOI_S3CL_KZ) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[INFNORM_POS_LT]; REAL_ARITH_TAC]);;

let MOI_S3CL_GLUE_INV = prove
 (`!(aa:int->real^N->bool) cc psi psi' c0.
     (!k. homeomorphism (moi_s3cl_sann (&1) (&2),aa k) (psi k,psi' k) /\
          IMAGE (psi k) (moi_s3cl_sann (&1) (&1)) = cc k /\
          IMAGE (psi k) (moi_s3cl_sann (&2) (&2)) = cc (k + &1) /\
          (!w. w IN moi_s3cl_sann (&1) (&1) ==> psi k (&2 % w) = psi (k + &1) w)) /\
     (!k. aa k INTER aa (k + &1) = cc (k + &1)) /\
     (!k m. k + &2 <= m ==> DISJOINT (aa k) (aa m)) /\
     (!k. ~(c0 IN aa k))
     ==> (!z. infnorm z < &1
              ==> moi_s3cl_fz psi c0 z IN c0 INSERT UNIONS {aa k | k IN (:int)} /\
                  moi_s3cl_gx aa psi' c0 (moi_s3cl_fz psi c0 z) = z) /\
         (!x. x IN c0 INSERT UNIONS {aa k | k IN (:int)}
              ==> infnorm(moi_s3cl_gx aa psi' c0 x) < &1 /\
                  moi_s3cl_fz psi c0 (moi_s3cl_gx aa psi' c0 x) = x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 (LABEL_TAC "ps") (CONJUNCTS_THEN2 (LABEL_TAC "int")
    (CONJUNCTS_THEN2 (LABEL_TAC "dis") (LABEL_TAC "c0")))) THEN
  SUBGOAL_THEN `!k z. z IN moi_s3cl_sann (moi_s3cl_al k) (moi_s3cl_al (k + &1))
                      ==> moi_s3cl_fz psi (c0:real^N) z =
                          psi k (moi_s3cl_scl (moi_s3cl_al k) (moi_s3cl_al (k + &1))
                                              (&1) (&2) z)`
  (LABEL_TAC "fp") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3CL_FZ_PIECE THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ps" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!k x. x IN (aa:int->real^N->bool) k
                      ==> moi_s3cl_gx aa psi' c0 x =
                          moi_s3cl_scl (&1) (&2) (moi_s3cl_al k) (moi_s3cl_al (k + &1))
                                       (psi' k x)`
  (LABEL_TAC "gp") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3CL_GX_PIECE THEN
    EXISTS_TAC `cc:int->real^N->bool` THEN EXISTS_TAC `psi:int->real^2->real^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN ASM_CASES_TAC `z:real^2 = vec 0` THENL
     [ASM_REWRITE_TAC[moi_s3cl_fz; moi_s3cl_gx]; ALL_TAC] THEN
    ABBREV_TAC `k = moi_s3cl_kz (z:real^2)` THEN
    SUBGOAL_THEN `z IN moi_s3cl_sann (moi_s3cl_al k) (moi_s3cl_al (k + &1))` ASSUME_TAC THENL
     [EXPAND_TAC "k" THEN MATCH_MP_TAC MOI_S3CL_MODEL_KZ THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "fp" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `z IN moi_s3cl_sann (moi_s3cl_al k) (moi_s3cl_al (k + &1))`)]) THEN
    MP_TAC(SPEC `k:int` MOI_S3CL_MODEL_SCL) THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
    USE_THEN "ps" (MP_TAC o CONJUNCT1 o SPEC `k:int`) THEN REWRITE_TAC[homeomorphism] THEN
    STRIP_TAC THEN
    ABBREV_TAC `y = moi_s3cl_scl (moi_s3cl_al k) (moi_s3cl_al (k + &1)) (&1) (&2) (z:real^2)` THEN
    SUBGOAL_THEN `(y:real^2) IN moi_s3cl_sann (&1) (&2)` ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(psi:int->real^2->real^N) k y IN aa k` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [DISJ2_TAC THEN EXISTS_TAC `(aa:int->real^N->bool) k` THEN
                    ASM_REWRITE_TAC[] THEN EXISTS_TAC `k:int` THEN REFL_TAC; ALL_TAC] THEN
    USE_THEN "gp" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `(psi:int->real^2->real^N) k y IN aa k`)]) THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "y" THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[moi_s3cl_gx; moi_s3cl_fz; INFNORM_0; REAL_LT_01]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th))) THEN
  USE_THEN "gp" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `(x:real^N) IN aa (k:int)`)]) THEN
  MP_TAC(SPEC `k:int` MOI_S3CL_MODEL_SCL) THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  USE_THEN "ps" (MP_TAC o CONJUNCT1 o SPEC `k:int`) THEN REWRITE_TAC[homeomorphism] THEN
  STRIP_TAC THEN
  ABBREV_TAC `y = moi_s3cl_scl (&1) (&2) (moi_s3cl_al k) (moi_s3cl_al (k + &1))
                               ((psi':int->real^N->real^2) k x)` THEN
  SUBGOAL_THEN `(y:real^2) IN moi_s3cl_sann (moi_s3cl_al k) (moi_s3cl_al (k + &1))`
  ASSUME_TAC THENL [EXPAND_TAC "y" THEN ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MOI_S3CL_MODEL_IN]; ALL_TAC] THEN
  USE_THEN "fp" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `(y:real^2) IN moi_s3cl_sann (moi_s3cl_al k) (moi_s3cl_al (k + &1))`)]) THEN
  EXPAND_TAC "y" THEN
  SUBGOAL_THEN `(psi':int->real^N->real^2) k x IN moi_s3cl_sann (&1) (&2)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ASM_SIMP_TAC[]]);;

let MOI_S3CL_SANN_CLOSED = prove
 (`!a b. closed(moi_s3cl_sann a b)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `moi_s3cl_sann a b =
                {z:real^2 | (lift o infnorm) z IN interval[lift a,lift b]}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; moi_s3cl_sann; IN_ELIM_THM; o_THM; IN_INTERVAL_1; LIFT_DROP];
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
    REWRITE_TAC[CLOSED_INTERVAL; ETA_AX; CONTINUOUS_AT_LIFT_INFNORM]]);;

let MOI_S3CL_SANN_COMPACT = prove
 (`!a b. compact(moi_s3cl_sann a b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; MOI_S3CL_SANN_CLOSED] THEN
  REWRITE_TAC[bounded; moi_s3cl_sann; IN_ELIM_THM] THEN
  EXISTS_TAC `&2 * abs b` THEN X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `z:real^2` NORM_LE_INFNORM) THEN REWRITE_TAC[DIMINDEX_2] THEN
  MP_TAC(SPEC `&2` SQRT_POS_LE) THEN
  SUBGOAL_THEN `sqrt(&2) <= &2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `z:real^2` INFNORM_POS_LE) THEN
  SUBGOAL_THEN `&0 <= infnorm(z:real^2) /\ infnorm z <= abs b` MP_TAC THENL
   [ASM_MESON_TAC[INFNORM_POS_LE; REAL_ARITH `x <= b ==> x <= abs b`]; ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&2) * infnorm(z:real^2) <= &2 * abs b` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_REAL_ARITH_TAC);;

let MOI_S3CL_INFNORM_OPEN = prove
 (`!a b. open {z:real^2 | a < infnorm z /\ infnorm z < b}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{z:real^2 | a < infnorm z /\ infnorm z < b} =
                {z:real^2 | (lift o infnorm) z IN interval(lift a,lift b)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; o_THM; IN_INTERVAL_1; LIFT_DROP];
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    REWRITE_TAC[OPEN_INTERVAL; ETA_AX; CONTINUOUS_AT_LIFT_INFNORM]]);;

let MOI_S3CL_SQUARE_OPEN = prove
 (`open {z:real^2 | infnorm z < &1} /\ convex {z:real^2 | infnorm z < &1} /\
   ~({z:real^2 | infnorm z < &1} = {})`,
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `{z:real^2 | infnorm z < &1} = {z:real^2 | -- &1 < infnorm z /\ infnorm z < &1}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
      MP_TAC(ISPEC `x:real^2` INFNORM_POS_LE) THEN REAL_ARITH_TAC;
      REWRITE_TAC[MOI_S3CL_INFNORM_OPEN]];
    REWRITE_TAC[convex; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `infnorm(u % (x:real^2)) + infnorm(v % (y:real^2))` THEN
    REWRITE_TAC[INFNORM_TRIANGLE; INFNORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= u ==> abs u = u`] THEN
    SUBGOAL_THEN `u * infnorm(x:real^2) <= u * &1 /\ v * infnorm(y:real^2) <= v * &1 /\
                  (u * infnorm(x:real^2) < u * &1 \/ v * infnorm(y:real^2) < v * &1)`
    MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ASM_CASES_TAC `&0 < u` THENL
         [DISJ1_TAC THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
          DISJ2_TAC THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC]];
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `vec 0:real^2` THEN
    REWRITE_TAC[INFNORM_0; REAL_LT_01]]);;

(* Continuity of the glued map fz on the open unit square.                   *)

let MOI_S3CL_GLUE_FCONT = prove
 (`!(aa:int->real^N->bool) cc psi psi' c0.
     (!k. homeomorphism (moi_s3cl_sann (&1) (&2),aa k) (psi k,psi' k) /\
          IMAGE (psi k) (moi_s3cl_sann (&1) (&1)) = cc k /\
          IMAGE (psi k) (moi_s3cl_sann (&2) (&2)) = cc (k + &1) /\
          (!w. w IN moi_s3cl_sann (&1) (&1) ==> psi k (&2 % w) = psi (k + &1) w)) /\
     (!e. &0 < e ==> ?K. !k. k <= K ==> aa k SUBSET ball(c0,e))
     ==> moi_s3cl_fz psi c0 continuous_on {z:real^2 | infnorm z < &1}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ps") (LABEL_TAC "low")) THEN
  SUBGOAL_THEN `!k z. z IN moi_s3cl_sann (moi_s3cl_al k) (moi_s3cl_al (k + &1))
                      ==> moi_s3cl_fz psi (c0:real^N) z =
                          psi k (moi_s3cl_scl (moi_s3cl_al k) (moi_s3cl_al (k + &1))
                                              (&1) (&2) z)`
  (LABEL_TAC "fp") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3CL_FZ_PIECE THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ps" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!k z. z IN moi_s3cl_sann (moi_s3cl_al k) (moi_s3cl_al (k + &1))
                      ==> moi_s3cl_fz psi (c0:real^N) z IN aa k`
  (LABEL_TAC "fin") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "fp" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `z IN moi_s3cl_sann (moi_s3cl_al k) (moi_s3cl_al (k + &1))`)]) THEN
    MP_TAC(SPEC `k:int` MOI_S3CL_MODEL_SCL) THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
    USE_THEN "ps" (MP_TAC o CONJUNCT1 o SPEC `k:int`) THEN REWRITE_TAC[homeomorphism] THEN
    STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* continuity off the centre *)
  SUBGOAL_THEN `moi_s3cl_fz psi (c0:real^N) continuous_on
                ({z:real^2 | infnorm z < &1} DELETE vec 0)` (LABEL_TAC "off") THENL
   [MATCH_MP_TAC(INST_TYPE [`:int`,`:K`] MOI_S3CL_PASTE) THEN
    MAP_EVERY EXISTS_TAC
     [`\k:int. (psi:int->real^2->real^N) k o
               moi_s3cl_scl (moi_s3cl_al k) (moi_s3cl_al (k + &1)) (&1) (&2)`;
      `\k:int. moi_s3cl_sann (moi_s3cl_al k) (moi_s3cl_al (k + &1))`; `(:int)`] THEN
    REWRITE_TAC[IN_UNIV; o_THM] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN STRIP_TAC THEN
      ABBREV_TAC `j = moi_s3cl_kz (z:real^2)` THEN
      SUBGOAL_THEN `moi_s3cl_al j <= infnorm(z:real^2) /\ infnorm z < moi_s3cl_al (j + &1)`
      STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "j" THEN MATCH_MP_TAC MOI_S3CL_KZ THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[INFNORM_POS_LT];
        ALL_TAC] THEN
      EXISTS_TAC `{y:real^2 | moi_s3cl_al (j - &1) < infnorm y /\
                              infnorm y < moi_s3cl_al (j + &1)}` THEN
      REWRITE_TAC[MOI_S3CL_INFNORM_OPEN; IN_ELIM_THM] THEN CONJ_TAC THENL
       [CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `moi_s3cl_al j` THEN
        ASM_REWRITE_TAC[MOI_S3CL_AL_LT] THEN INT_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j - &1,j:int}` THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; SUBSET; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
      X_GEN_TAC `m:int` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM;
                                        moi_s3cl_sann] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `moi_s3cl_al m < moi_s3cl_al (j + &1) /\
                    moi_s3cl_al (j - &1) < moi_s3cl_al (m + &1)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; REWRITE_TAC[MOI_S3CL_AL_LT] THEN INT_ARITH_TAC];
      X_GEN_TAC `k:int` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_SUBSET THEN REWRITE_TAC[MOI_S3CL_SANN_CLOSED] THEN
        REWRITE_TAC[SUBSET; IN_DELETE; IN_ELIM_THM] THEN MESON_TAC[MOI_S3CL_MODEL_IN];
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        MP_TAC(SPEC `k:int` MOI_S3CL_MODEL_SCL) THEN REWRITE_TAC[homeomorphism] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "ps" (MP_TAC o CONJUNCT1 o SPEC `k:int`) THEN
        REWRITE_TAC[homeomorphism] THEN SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`i:int`; `j:int`; `z:real^2`] THEN REWRITE_TAC[IN_INTER] THEN
      STRIP_TAC THEN USE_THEN "fp" (fun th ->
        REWRITE_TAC[GSYM(MATCH_MP th (ASSUME
          `z IN moi_s3cl_sann (moi_s3cl_al i) (moi_s3cl_al (i + &1))`));
                    GSYM(MATCH_MP th (ASSUME
          `z IN moi_s3cl_sann (moi_s3cl_al j) (moi_s3cl_al (j + &1))`))]);
      X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN STRIP_TAC THEN
      EXISTS_TAC `moi_s3cl_kz (z:real^2)` THEN
      SUBGOAL_THEN `z IN moi_s3cl_sann (moi_s3cl_al (moi_s3cl_kz z))
                                      (moi_s3cl_al (moi_s3cl_kz z + &1))` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_S3CL_MODEL_KZ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "fp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN X_GEN_TAC `z:real^2` THEN
  DISCH_TAC THEN ASM_CASES_TAC `z:real^2 = vec 0` THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`moi_s3cl_fz psi (c0:real^N)`; `z:real^2`;
                   `{z:real^2 | infnorm z < &1}`;
                   `{z:real^2 | infnorm z < &1} DELETE vec 0`] CONTINUOUS_WITHIN_OPEN_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_DELETE] THEN
      SUBGOAL_THEN `{z:real^2 | infnorm z < &1} DELETE vec 0 =
                    {z:real^2 | infnorm z < &1} INTER ((:real^2) DELETE vec 0)`
      SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN SIMP_TAC[OPEN_DELETE; OPEN_UNIV];
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      USE_THEN "off" (MP_TAC o REWRITE_RULE[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DELETE]]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[CONTINUOUS_WITHIN; LIM_WITHIN] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "low" (X_CHOOSE_TAC `K:int` o C MATCH_MP (ASSUME `&0 < e`)) THEN
  EXISTS_TAC `moi_s3cl_al K` THEN REWRITE_TAC[MOI_S3CL_AL_BOUNDS] THEN
  X_GEN_TAC `y:real^2` THEN REWRITE_TAC[IN_ELIM_THM; DIST_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^2 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&0 < norm(vec 0:real^2)` THEN
    REWRITE_TAC[NORM_0; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s3cl_fz psi (c0:real^N) (vec 0) = c0` SUBST1_TAC THENL
   [REWRITE_TAC[moi_s3cl_fz]; ALL_TAC] THEN
  ABBREV_TAC `j = moi_s3cl_kz (y:real^2)` THEN
  SUBGOAL_THEN `y IN moi_s3cl_sann (moi_s3cl_al j) (moi_s3cl_al (j + &1))` ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN MATCH_MP_TAC MOI_S3CL_MODEL_KZ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `j:int <= K` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_S3CL_AL_LE] THEN
    UNDISCH_TAC `y IN moi_s3cl_sann (moi_s3cl_al j) (moi_s3cl_al (j + &1))` THEN
    REWRITE_TAC[moi_s3cl_sann; IN_ELIM_THM] THEN
    MP_TAC(ISPEC `y:real^2` INFNORM_LE_NORM) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s3cl_fz psi (c0:real^N) y IN ball(c0,e)` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `j:int <= K`) o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `ball(c0:real^N,e)`)) (concl th))) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "fin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_BALL] THEN MESON_TAC[DIST_SYM]]);;

(* norm <= 2 infnorm in real^2.                                              *)

let MOI_S3CL_NORM_LE_2INF = prove
 (`!z:real^2. norm z <= &2 * infnorm z`,
  GEN_TAC THEN MP_TAC(ISPEC `z:real^2` NORM_LE_INFNORM) THEN
  REWRITE_TAC[DIMINDEX_2] THEN
  SUBGOAL_THEN `sqrt(&2) <= &2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `z:real^2` INFNORM_POS_LE) THEN
  SUBGOAL_THEN `sqrt(&2) * infnorm(z:real^2) <= &2 * infnorm z` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[INFNORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* Continuity of the glued map gx on the chain plus its centre.               *)

let MOI_S3CL_GLUE_GCONT = prove
 (`!(aa:int->real^N->bool) cc psi psi' c0.
     (!k. homeomorphism (moi_s3cl_sann (&1) (&2),aa k) (psi k,psi' k) /\
          IMAGE (psi k) (moi_s3cl_sann (&1) (&1)) = cc k /\
          IMAGE (psi k) (moi_s3cl_sann (&2) (&2)) = cc (k + &1) /\
          (!w. w IN moi_s3cl_sann (&1) (&1) ==> psi k (&2 % w) = psi (k + &1) w)) /\
     (!k. aa k INTER aa (k + &1) = cc (k + &1)) /\
     (!k m. k + &2 <= m ==> DISJOINT (aa k) (aa m)) /\
     (!k. ~(c0 IN aa k)) /\
     (!k x. x IN aa k ==> ?u. open u /\ x IN u /\ FINITE {m | ~(aa m INTER u = {})}) /\
     (!K. ?e. &0 < e /\ !k. K <= k ==> DISJOINT (aa k) (ball(c0,e)))
     ==> moi_s3cl_gx aa psi' c0 continuous_on (c0 INSERT UNIONS {aa k | k IN (:int)})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 (LABEL_TAC "ps") (CONJUNCTS_THEN2 (LABEL_TAC "int")
    (CONJUNCTS_THEN2 (LABEL_TAC "dis") (CONJUNCTS_THEN2 (LABEL_TAC "c0")
    (CONJUNCTS_THEN2 (LABEL_TAC "lf") (LABEL_TAC "far")))))) THEN
  SUBGOAL_THEN `!k x. x IN (aa:int->real^N->bool) k
                      ==> moi_s3cl_gx aa psi' c0 x =
                          moi_s3cl_scl (&1) (&2) (moi_s3cl_al k) (moi_s3cl_al (k + &1))
                                       (psi' k x)`
  (LABEL_TAC "gp") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3CL_GX_PIECE THEN
    EXISTS_TAC `cc:int->real^N->bool` THEN EXISTS_TAC `psi:int->real^2->real^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. compact((aa:int->real^N->bool) k)` (LABEL_TAC "cpt") THENL
   [GEN_TAC THEN USE_THEN "ps" (MP_TAC o CONJUNCT1 o SPEC `k:int`) THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `(aa:int->real^N->bool) k`)) (rand(concl th)) &&
      is_comb(lhs(concl th)) && can (find_term ((=) `(psi:int->real^2->real^N) k`))
        (lhs(concl th)))) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[MOI_S3CL_SANN_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s3cl_gx aa psi' (c0:real^N) continuous_on
    ((c0 INSERT UNIONS {aa k | k IN (:int)}) DELETE c0)` (LABEL_TAC "off") THENL
   [MATCH_MP_TAC(INST_TYPE [`:int`,`:K`] MOI_S3CL_PASTE) THEN
    MAP_EVERY EXISTS_TAC
     [`\k:int. moi_s3cl_scl (&1) (&2) (moi_s3cl_al k) (moi_s3cl_al (k + &1)) o
               (psi':int->real^N->real^2) k`;
      `aa:int->real^N->bool`; `(:int)`] THEN
    REWRITE_TAC[IN_UNIV; o_THM] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN
      REWRITE_TAC[IN_DELETE; IN_INSERT; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
      STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th))) THEN
      USE_THEN "lf" (MATCH_MP_TAC o SPEC `k:int`) THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `k:int` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_SUBSET THEN USE_THEN "cpt" (fun th ->
          REWRITE_TAC[MATCH_MP COMPACT_IMP_CLOSED (SPEC `k:int` th)]) THEN
        REWRITE_TAC[SUBSET; IN_DELETE; IN_INSERT; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
        X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
         [DISJ2_TAC THEN EXISTS_TAC `(aa:int->real^N->bool) k` THEN ASM_REWRITE_TAC[] THEN
          EXISTS_TAC `k:int` THEN REFL_TAC;
          DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]];
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        USE_THEN "ps" (MP_TAC o CONJUNCT1 o SPEC `k:int`) THEN
        REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPEC `k:int` MOI_S3CL_MODEL_SCL) THEN REWRITE_TAC[homeomorphism] THEN
        SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`i:int`; `j:int`; `x:real^N`] THEN REWRITE_TAC[IN_INTER] THEN
      STRIP_TAC THEN USE_THEN "gp" (fun th ->
        REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `(x:real^N) IN aa (i:int)`));
                    GSYM(MATCH_MP th (ASSUME `(x:real^N) IN aa (j:int)`))]);
      X_GEN_TAC `x:real^N` THEN
      REWRITE_TAC[IN_DELETE; IN_INSERT; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
      STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th))) THEN
      EXISTS_TAC `k:int` THEN ASM_REWRITE_TAC[] THEN USE_THEN "gp" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN X_GEN_TAC `x:real^N` THEN
  DISCH_TAC THEN ASM_CASES_TAC `x:real^N = c0` THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`moi_s3cl_gx aa psi' (c0:real^N)`; `x:real^N`;
                   `c0 INSERT UNIONS {(aa:int->real^N->bool) k | k IN (:int)}`;
                   `(c0 INSERT UNIONS {(aa:int->real^N->bool) k | k IN (:int)}) DELETE c0`]
                  CONTINUOUS_WITHIN_OPEN_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_DELETE] THEN
      SUBGOAL_THEN `(c0 INSERT UNIONS {(aa:int->real^N->bool) k | k IN (:int)}) DELETE c0 =
                    (c0 INSERT UNIONS {aa k | k IN (:int)}) INTER ((:real^N) DELETE c0)`
      SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN SIMP_TAC[OPEN_DELETE; OPEN_UNIV];
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      USE_THEN "off" (MP_TAC o REWRITE_RULE[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DELETE]]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[CONTINUOUS_WITHIN; LIM_WITHIN] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `e / &2` MOI_S3CL_AL_LOW) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `K:int`)] THEN
  USE_THEN "far" (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC o SPEC `K:int`) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_INSERT; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN STRIP_TAC THENL
   [UNDISCH_TAC `&0 < dist(y:real^N,c0)` THEN ASM_REWRITE_TAC[DIST_REFL; REAL_LT_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    can (find_term ((=) `(aa:int->real^N->bool) k`)) (concl th))) THEN
  SUBGOAL_THEN `moi_s3cl_gx aa psi' (c0:real^N) c0 = vec 0` SUBST1_TAC THENL
   [REWRITE_TAC[moi_s3cl_gx]; ALL_TAC] THEN
  SUBGOAL_THEN `k:int < K` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_NOT_LE] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `K:int <= k`) o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `d:real`)) (concl th))) THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_BALL; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  USE_THEN "gp" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(y:real^N) IN aa (k:int)`)]) THEN
  REWRITE_TAC[DIST_0] THEN
  MP_TAC(SPEC `k:int` MOI_S3CL_MODEL_SCL) THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  USE_THEN "ps" (MP_TAC o CONJUNCT1 o SPEC `k:int`) THEN REWRITE_TAC[homeomorphism] THEN
  STRIP_TAC THEN
  ABBREV_TAC `z = moi_s3cl_scl (&1) (&2) (moi_s3cl_al k) (moi_s3cl_al (k + &1))
                               ((psi':int->real^N->real^2) k y)` THEN
  SUBGOAL_THEN `(z:real^2) IN moi_s3cl_sann (moi_s3cl_al k) (moi_s3cl_al (k + &1))`
  MP_TAC THENL [EXPAND_TAC "z" THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_s3cl_sann; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s3cl_al (k + &1) <= moi_s3cl_al K` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S3CL_AL_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `z:real^2` MOI_S3CL_NORM_LE_2INF) THEN ASM_REAL_ARITH_TAC);;

(* A bi-infinite chain of annuli converging to a point c0 at one end and     *)
(* locally finite away from c0, with parametrizations agreeing on the       *)
(* shared circles, plus c0, is an open disk.                                 *)

let MOI_S3CL_GLUE = prove
 (`!(aa:int->real^N->bool) cc psi psi' c0.
     (!k. homeomorphism (moi_s3cl_sann (&1) (&2),aa k) (psi k,psi' k) /\
          IMAGE (psi k) (moi_s3cl_sann (&1) (&1)) = cc k /\
          IMAGE (psi k) (moi_s3cl_sann (&2) (&2)) = cc (k + &1) /\
          (!w. w IN moi_s3cl_sann (&1) (&1) ==> psi k (&2 % w) = psi (k + &1) w)) /\
     (!k. aa k INTER aa (k + &1) = cc (k + &1)) /\
     (!k m. k + &2 <= m ==> DISJOINT (aa k) (aa m)) /\
     (!k. ~(c0 IN aa k)) /\
     (!k x. x IN aa k ==> ?u. open u /\ x IN u /\ FINITE {m | ~(aa m INTER u = {})}) /\
     (!e. &0 < e ==> ?K. !k. k <= K ==> aa k SUBSET ball(c0,e)) /\
     (!K. ?e. &0 < e /\ !k. K <= k ==> DISJOINT (aa k) (ball(c0,e)))
     ==> (c0 INSERT UNIONS {aa k | k IN (:int)}) homeomorphic ball(vec 0:real^2,&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c0 INSERT UNIONS {(aa:int->real^N->bool) k | k IN (:int)}`;
                 `{z:real^2 | infnorm z < &1}`; `ball(vec 0:real^2,&1)`]
                HOMEOMORPHIC_TRANS) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC HOMEOMORPHIC_CONVEX_OPEN_SETS THEN
    REWRITE_TAC[MOI_S3CL_SQUARE_OPEN; OPEN_BALL; CONVEX_BALL; BALL_EQ_EMPTY] THEN
    REAL_ARITH_TAC] THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
  MAP_EVERY EXISTS_TAC [`moi_s3cl_fz psi (c0:real^N)`; `moi_s3cl_gx aa psi' (c0:real^N)`] THEN
  MP_TAC(ISPECL [`aa:int->real^N->bool`; `cc:int->real^N->bool`; `psi:int->real^2->real^N`;
                 `psi':int->real^N->real^2`; `c0:real^N`] MOI_S3CL_GLUE_INV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`aa:int->real^N->bool`; `cc:int->real^N->bool`; `psi:int->real^2->real^N`;
                 `psi':int->real^N->real^2`; `c0:real^N`] MOI_S3CL_GLUE_FCONT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`aa:int->real^N->bool`; `cc:int->real^N->bool`; `psi:int->real^2->real^N`;
                 `psi':int->real^N->real^2`; `c0:real^N`] MOI_S3CL_GLUE_GCONT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_REWRITE_TAC[homeomorphism; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THEN TRY(GEN_REWRITE_TAC I [EXTENSION]) THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN GEN_TAC THEN ASM_MESON_TAC[]);;

(* The open-disk theorem for chains of square-annulus images.               *)

let MOI_S3CL_CHAIN_DISK = prove
 (`!(aa:int->real^N->bool) cc c0.
     (!k. ?f f'. homeomorphism (moi_s3cl_sann (&1) (&2),aa k) (f,f') /\
                 IMAGE f (moi_s3cl_sann (&1) (&1)) = cc k /\
                 IMAGE f (moi_s3cl_sann (&2) (&2)) = cc (k + &1)) /\
     (!k. aa k INTER aa (k + &1) = cc (k + &1)) /\
     (!k m. k + &2 <= m ==> DISJOINT (aa k) (aa m)) /\
     (!k. ~(c0 IN aa k)) /\
     (!k x. x IN aa k ==> ?u. open u /\ x IN u /\ FINITE {m | ~(aa m INTER u = {})}) /\
     (!e. &0 < e ==> ?K. !k. k <= K ==> aa k SUBSET ball(c0,e)) /\
     (!K. ?e. &0 < e /\ !k. K <= k ==> DISJOINT (aa k) (ball(c0,e)))
     ==> (c0 INSERT UNIONS {aa k | k IN (:int)}) homeomorphic ball(vec 0:real^2,&1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_S3CL_CHAIN_PARAM) THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:int->real^2->real^N` (X_CHOOSE_TAC `psi':int->real^N->real^2`)) THEN
  MATCH_MP_TAC MOI_S3CL_GLUE THEN
  MAP_EVERY EXISTS_TAC [`cc:int->real^N->bool`; `psi:int->real^2->real^N`;
                        `psi':int->real^N->real^2`] THEN
  ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Part 5. The Moise chain indexed by Z: A(2i) = hh i, A(2i+1) = bb i with  *)
(* ends C(2i) = jl i, C(2i+1) = jh i; the hypotheses of MOI_S3CL_CHAIN_DISK *)
(* from the model, the tower and the chain; the chain set is an open disk.  *)
(* ------------------------------------------------------------------------- *)

let moi_s3cl_ann = new_definition
 `moi_s3cl_ann (hh:int->real^3->bool) (bb:int->real^3->bool) (k:int) =
    if k rem &2 = &0 then hh (k div &2) else bb (k div &2)`;;

let moi_s3cl_circ = new_definition
 `moi_s3cl_circ (jl:int->real^3->bool) (jh:int->real^3->bool) (k:int) =
    if k rem &2 = &0 then jl (k div &2) else jh (k div &2)`;;
(* The chain indexed by k in Z: A(2i) = hh i, A(2i+1) = bb i, with ends     *)
(* C(2i) = jl i and C(2i+1) = jh i.                                          *)

let MOI_S3CL_PARITY = prove
 (`!i:int. (&2 * i) div &2 = i /\ (&2 * i) rem &2 = &0 /\
           (&2 * i + &1) div &2 = i /\ (&2 * i + &1) rem &2 = &1`,
  GEN_TAC THEN CONJ_TAC THENL [ALL_TAC; CONJ_TAC] THENL
   [MP_TAC(SPECL [`&2 * i:int`; `&2:int`; `i:int`; `&0:int`] INT_DIVMOD_UNIQ);
    MP_TAC(SPECL [`&2 * i:int`; `&2:int`; `i:int`; `&0:int`] INT_DIVMOD_UNIQ);
    MP_TAC(SPECL [`&2 * i + &1:int`; `&2:int`; `i:int`; `&1:int`] INT_DIVMOD_UNIQ)] THEN
  INT_ARITH_TAC);;

let MOI_S3CL_PARITY_CASES = prove
 (`!k:int. k = &2 * (k div &2) /\ k rem &2 = &0 \/
           k = &2 * (k div &2) + &1 /\ k rem &2 = &1`,
  GEN_TAC THEN MP_TAC(SPECL [`k:int`; `&2:int`] INT_DIVISION) THEN
  MP_TAC(SPEC `k:int` INT_REM_2_CASES) THEN INT_ARITH_TAC);;

let MOI_S3CL_ANN_CIRC = prove
 (`!hh bb jl jh i.
     moi_s3cl_ann hh bb (&2 * i) = hh i /\ moi_s3cl_ann hh bb (&2 * i + &1) = bb i /\
     moi_s3cl_circ jl jh (&2 * i) = jl i /\ moi_s3cl_circ jl jh (&2 * i + &1) = jh i`,
  REWRITE_TAC[moi_s3cl_ann; moi_s3cl_circ; MOI_S3CL_PARITY] THEN
  REWRITE_TAC[INT_ARITH `~(&1:int = &0)`]);;

let MOI_S3CL_INT_CASES = prove
 (`!P. (!i. P(&2 * i)) /\ (!i. P(&2 * i + &1)) ==> !k:int. P k`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(SPEC `k:int` MOI_S3CL_PARITY_CASES) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC)) THEN ASM_REWRITE_TAC[]);;

let MOI_S3CL_UNIONS_ANN = prove
 (`!hh bb. UNIONS {moi_s3cl_ann hh bb k | k IN (:int)} =
           UNIONS {hh i UNION bb i | i IN (:int)}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_UNIV] THENL
   [MATCH_MP_TAC MOI_S3CL_INT_CASES THEN REWRITE_TAC[MOI_S3CL_ANN_CIRC] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN CONJ_TAC THEN
    MAP_EVERY X_GEN_TAC [`i:int`; `x:real^3`] THEN DISCH_TAC THEN
    EXISTS_TAC `(hh:int->real^3->bool) i UNION bb i` THEN
    ASM_REWRITE_TAC[IN_UNION] THEN EXISTS_TAC `i:int` THEN REFL_TAC;
    X_GEN_TAC `i:int` THEN REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_TAC THENL
     [EXISTS_TAC `moi_s3cl_ann hh bb (&2 * i)` THEN CONJ_TAC THENL
       [EXISTS_TAC `&2 * i:int` THEN REFL_TAC; ASM_REWRITE_TAC[MOI_S3CL_ANN_CIRC]];
      EXISTS_TAC `moi_s3cl_ann hh bb (&2 * i + &1)` THEN CONJ_TAC THENL
       [EXISTS_TAC `&2 * i + &1:int` THEN REFL_TAC; ASM_REWRITE_TAC[MOI_S3CL_ANN_CIRC]]]]);;
(* The annuli: a PL annulus with ends is a homeomorphic image of the square *)
(* annulus 1 <= infnorm <= 2 with its two boundary squares as the ends.      *)

let MOI_S3CL_ANNULUS_PARAM = prove
 (`!(a:real^N->bool) j0 j1.
     pl_annulus_with_ends a j0 j1
     ==> ?f f'. homeomorphism (moi_s3cl_sann (&1) (&2),a) (f,f') /\
                IMAGE f (moi_s3cl_sann (&1) (&1)) = j0 /\
                IMAGE f (moi_s3cl_sann (&2) (&2)) = j1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pl_annulus_with_ends; pl_homeomorphism; MOI_S3CL_SQ] THEN
  MP_TAC(SPEC `&1` MOI_S3CL_RF) THEN MP_TAC(SPEC `&2` MOI_S3CL_RF) THEN
  REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MESON_TAC[]);;

let MOI_S3CL_ANNULUS_ENDS = prove
 (`!(a:real^N->bool) j0 j1.
     pl_annulus_with_ends a j0 j1 ==> j0 SUBSET a /\ j1 SUBSET a`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_S3CL_ANNULUS_PARAM) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s3cl_sann (&1) (&1) SUBSET moi_s3cl_sann (&1) (&2) /\
                moi_s3cl_sann (&2) (&2) SUBSET moi_s3cl_sann (&1) (&2)` MP_TAC THENL
   [REWRITE_TAC[moi_s3cl_sann; SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ASM SET_TAC[]]);;

(* The revolved cells lie in v and in the model.                            *)

let MOI_S3CL_REV_CYL = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> !j. revolution (dd j) SUBSET v /\ revolution (dd j) SUBSET moi_s32_cyl`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "tt" o MATCH_MP MOI_S3GF_TOWER_TORI)) THEN
  REWRITE_TAC[moi_s32_model] THEN STRIP_TAC THEN X_GEN_TAC `j:int` THEN
  USE_THEN "tt" (STRIP_ASSUME_TAC o SPEC `j:int`) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SUBSET_TRANS; INTERIOR_SUBSET]);;

(* The annuli hh i are pairwise disjoint (they lie in g(rev dd(2i)), and    *)
(* the cells dd(2i), dd(2k) are disjoint for i <> k).                       *)

let MOI_S3CL_HH_DISJ = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> !i k. ~(i = k) ==> DISJOINT (hh i) (hh k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`]
    MOI_S3GF_CHAIN_PIECES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "pc" o CONJUNCT1) THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3CL_REV_CYL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "rc") THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s32_model]) THEN
  DISCH_THEN(LABEL_TAC "inj" o CONJUNCT1 o CONJUNCT2) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `DISJOINT ((dd:int->real^3->bool) (&2 * i)) (dd (&2 * k))` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_tower (g:real^3->real^3) v pp dd s2` THEN
    REWRITE_TAC[moi_s32_tower] THEN
    DISCH_THEN(fun th -> let th5 = el 5 (CONJUNCTS th) in
      MP_TAC(SPECL [`&2 * i:int`; `&2 * k:int`] th5) THEN
      MP_TAC(SPECL [`&2 * k:int`; `&2 * i:int`] th5)) THEN
    SUBGOAL_THEN `&2 * i + &2 <= &2 * k \/ &2 * k + &2 <= &2 * i:int` MP_TAC THENL
     [UNDISCH_TAC `~(i:int = k)` THEN INT_ARITH_TAC; ALL_TAC] THEN
    MESON_TAC[DISJOINT_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `moi_s32_cyl`; `(dd:int->real^3->bool) (&2 * i)`;
                 `(dd:int->real^3->bool) (&2 * k)`] MOI_STD_IMAGE_REV_DISJOINT) THEN
  ANTS_TAC THENL
   [USE_THEN "rc" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "inj" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[GSYM DISJOINT];
    ALL_TAC] THEN
  USE_THEN "pc" (fun th -> MP_TAC(SPEC `i:int` th) THEN MP_TAC(SPEC `k:int` th)) THEN
  SET_TAC[]);;

(* The ends of the annuli; hh i lies in the even boundaries K.              *)

let MOI_S3CL_CHAIN_ENDS = prove
 (`!(g:real^3->real^3) dd s2 hh bb jl jh.
     moi_s32_chain g dd s2 hh bb jl jh
     ==> !i. hh i SUBSET moi_s32_evens s2 /\
             jl i SUBSET hh i /\ jh i SUBSET hh i /\
             jh i SUBSET bb i /\ jl (i + &1) SUBSET bb i /\
             bb i INTER moi_s32_evens s2 = jh i UNION jl (i + &1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_chain] THEN
  DISCH_THEN(LABEL_TAC "c" o CONJUNCT1) THEN X_GEN_TAC `i:int` THEN
  USE_THEN "c" (STRIP_ASSUME_TAC o SPEC `i:int`) THEN
  SUBGOAL_THEN `(jl:int->real^3->bool) i SUBSET hh i /\ (jh:int->real^3->bool) i SUBSET hh i`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3CL_ANNULUS_ENDS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(jh:int->real^3->bool) i SUBSET bb i /\
                (jl:int->real^3->bool) (i + &1) SUBSET bb i`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3CL_ANNULUS_ENDS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `frontier((s2:int->real^3->bool) (&2 * i)) SUBSET moi_s32_evens s2`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s32_evens; SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_TRANS]);;

(* hh j meets bb i only for j = i (in jh i) and j = i + 1 (in jl(i + 1)).   *)

let MOI_S3CL_HB = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> (!i j. ~(j = i) /\ ~(j = i + &1) ==> DISJOINT (hh j) (bb i)) /\
         (!i. hh i INTER bb i = jh i) /\
         (!i. bb i INTER hh (i + &1) = jl (i + &1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "hd" o MATCH_MP MOI_S3CL_HH_DISJ) THEN
  FIRST_ASSUM(LABEL_TAC "ce" o MATCH_MP MOI_S3CL_CHAIN_ENDS o CONJUNCT2 o CONJUNCT2) THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:int`; `j:int`] THEN STRIP_TAC THEN
    USE_THEN "hd" (fun th -> MP_TAC(SPECL [`j:int`; `i:int`] th) THEN
                             MP_TAC(SPECL [`j:int`; `i + &1:int`] th)) THEN
    REWRITE_TAC[ASSUME `~(j:int = i)`; ASSUME `~(j:int = i + &1)`] THEN
    USE_THEN "ce" (fun th -> let c t = CONJUNCTS(SPEC t th) in
      MP_TAC(end_itlist CONJ [el 0 (c `j:int`); el 2 (c `i:int`); el 5 (c `i:int`);
                              el 1 (c `i + &1:int`)])) THEN
    SET_TAC[];
    X_GEN_TAC `i:int` THEN
    USE_THEN "hd" (MP_TAC o SPECL [`i:int`; `i + &1:int`]) THEN
    REWRITE_TAC[INT_ARITH `~(i:int = i + &1)`] THEN
    USE_THEN "ce" (fun th -> let c t = CONJUNCTS(SPEC t th) in
      MP_TAC(end_itlist CONJ [el 0 (c `i:int`); el 2 (c `i:int`); el 3 (c `i:int`);
                              el 5 (c `i:int`); el 1 (c `i + &1:int`)])) THEN
    SET_TAC[];
    X_GEN_TAC `i:int` THEN
    USE_THEN "hd" (MP_TAC o SPECL [`i + &1:int`; `i:int`]) THEN
    REWRITE_TAC[INT_ARITH `~(i + &1:int = i)`] THEN
    USE_THEN "ce" (fun th -> let c t = CONJUNCTS(SPEC t th) in
      MP_TAC(end_itlist CONJ [el 0 (c `i + &1:int`); el 1 (c `i + &1:int`); el 2 (c `i:int`);
                              el 4 (c `i:int`); el 5 (c `i:int`)])) THEN
    SET_TAC[]]);;

(* The chain hypotheses of MOI_S3CL_CHAIN_DISK for A = moi_s3cl_ann hh bb  *)
(* and C = moi_s3cl_circ jl jh: parametrizations, consecutive intersections, *)
(* disjointness two apart, and the centre outside every annulus.            *)

let MOI_S3CL_AA_PARAM = prove
 (`!(g:real^3->real^3) dd s2 hh bb jl jh.
     moi_s32_chain g dd s2 hh bb jl jh
     ==> !k. ?f f'. homeomorphism (moi_s3cl_sann (&1) (&2),moi_s3cl_ann hh bb k) (f,f') /\
                    IMAGE f (moi_s3cl_sann (&1) (&1)) = moi_s3cl_circ jl jh k /\
                    IMAGE f (moi_s3cl_sann (&2) (&2)) = moi_s3cl_circ jl jh (k + &1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_chain] THEN
  DISCH_THEN(LABEL_TAC "c" o CONJUNCT1) THEN MATCH_MP_TAC MOI_S3CL_INT_CASES THEN
  REWRITE_TAC[MOI_S3CL_ANN_CIRC; INT_ARITH `(&2 * i + &1) + &1 = &2 * (i + &1):int`] THEN
  CONJ_TAC THEN X_GEN_TAC `i:int` THEN MATCH_MP_TAC MOI_S3CL_ANNULUS_PARAM THEN
  USE_THEN "c" (MP_TAC o SPEC `i:int`) THEN SIMP_TAC[]);;

let MOI_S3CL_AA_INT = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> !k. moi_s3cl_ann hh bb k INTER moi_s3cl_ann hh bb (k + &1) =
             moi_s3cl_circ jl jh (k + &1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_S3CL_HB) THEN
  STRIP_TAC THEN MATCH_MP_TAC MOI_S3CL_INT_CASES THEN
  ASM_REWRITE_TAC[MOI_S3CL_ANN_CIRC; INT_ARITH `(&2 * i + &1) + &1 = &2 * (i + &1):int`]);;

let MOI_S3CL_AA_DIS = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> !k m. k + &2 <= m ==> DISJOINT (moi_s3cl_ann hh bb k) (moi_s3cl_ann hh bb m)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "hd" o MATCH_MP MOI_S3CL_HH_DISJ) THEN
  FIRST_ASSUM(LABEL_TAC "hb" o CONJUNCT1 o MATCH_MP MOI_S3CL_HB) THEN
  SUBGOAL_THEN `!i k. ~(i = k) ==> DISJOINT ((bb:int->real^3->bool) i) (bb k)`
  (LABEL_TAC "bd") THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN REWRITE_TAC[moi_s32_chain] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3CL_INT_CASES THEN CONJ_TAC THEN X_GEN_TAC `i:int` THEN
  MATCH_MP_TAC MOI_S3CL_INT_CASES THEN CONJ_TAC THEN X_GEN_TAC `j:int` THEN
  REWRITE_TAC[MOI_S3CL_ANN_CIRC] THEN DISCH_TAC THENL
   [USE_THEN "hd" MATCH_MP_TAC THEN ASM_INT_ARITH_TAC;
    USE_THEN "hb" MATCH_MP_TAC THEN ASM_INT_ARITH_TAC;
    ONCE_REWRITE_TAC[DISJOINT_SYM] THEN USE_THEN "hb" MATCH_MP_TAC THEN ASM_INT_ARITH_TAC;
    USE_THEN "bd" MATCH_MP_TAC THEN ASM_INT_ARITH_TAC]);;

let MOI_S3CL_AA_C0 = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> !k. moi_s3cl_ann hh bb k SUBSET IMAGE g v /\
             ~(g (vec 0) IN moi_s3cl_ann hh bb k)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(!i:int. (hh:int->real^3->bool) i SUBSET IMAGE (g:real^3->real^3) v) /\
                (!i:int. (bb:int->real^3->bool) i SUBSET IMAGE (g:real^3->real^3) v) /\
                ~(g (vec 0) IN IMAGE g v)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3GF_CHAIN_PIECES) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3GF_MODEL_V o CONJUNCT1) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3CL_INT_CASES THEN REWRITE_TAC[MOI_S3CL_ANN_CIRC] THEN
  CONJ_TAC THEN X_GEN_TAC `i:int` THEN ASM SET_TAC[]);;
(* ------------------------------------------------------------------------- *)
(* The two ends of the tower in the model.  The points pp i = r_i e1 have    *)
(* norm r_i, increasing in i with infimum 0; each cell dd i is a compact     *)
(* connected planar disk in the half plane containing pp i; revolution keeps *)
(* the norm; compact sets off the centre and the rim (spheres of radius     *)
(* rho < 1, small closed balls in v) meet only finitely many revolved cells. *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CL_PP_FACTS = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_tower g v pp dd s2
     ==> (!i. &0 < (pp i)$1 /\ (pp i)$1 < &1 /\ norm(pp i) = (pp i)$1) /\
         (!i j. i <= j ==> (pp i)$1 <= (pp j)$1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_tower] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "r")
    (CONJUNCTS_THEN2 (LABEL_TAC "inc") (K ALL_TAC)))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:int` THEN
    USE_THEN "r" (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC o SPEC `i:int`) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT; NORM_MUL] THEN
    SIMP_TAC[BASIS_COMPONENT; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i n. ((pp:int->real^3) i)$1 <= (pp (i + &n))$1` ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[INT_ADD_RID; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `((pp:int->real^3) (i + &n))$1` THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_SUC; INT_ADD_ASSOC] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "inc" (ACCEPT_TAC o SPEC `i + &n:int`);
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `j - i:int` INT_OF_NUM_EXISTS) THEN ASM_REWRITE_TAC[INT_SUB_LE] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  SUBGOAL_THEN `j:int = i + &n` SUBST1_TAC THENL [ASM_INT_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let MOI_S3CL_DD_FACTS = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_tower g v pp dd s2
     ==> !j. dd j SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1} /\
             compact (dd j) /\ connected (dd j) /\ pp j IN dd j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_tower] THEN
  DISCH_THEN(LABEL_TAC "cc" o CONJUNCT1) THEN X_GEN_TAC `j:int` THEN
  USE_THEN "cc" (MP_TAC o SPEC `j:int`) THEN
  REWRITE_TAC[canonical_configuration; planar_cell_chain] THEN
  DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT1 o CONJUNCT1) THEN
  REWRITE_TAC[ARITH; INT_ADD_RID; ADD_CLAUSES] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (term_match [] `disk_with_boundary (a:real^3->bool) b`) (concl th))) THEN
    REWRITE_TAC[disk_with_boundary; homeomorphism] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) && rhs(concl th) = `(dd:int->real^3->bool) j`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE; CONNECTED_CONTINUOUS_IMAGE; COMPACT_CBALL;
                 CONNECTED_CBALL];
    ASM_MESON_TAC[ENDS_IN_SEGMENT; RELATIVE_INTERIOR_SUBSET; SUBSET]]);;

let MOI_S3CL_REV_NORM = prove
 (`!(x:real^3->bool) p. p IN revolution x ==> ?q. q IN x /\ norm p = norm q`,
  REWRITE_TAC[revolution; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `q:real^3` THEN ASM_REWRITE_TAC[NORM_EQ; DOT_3] THEN
  UNDISCH_TAC `(q:real^3)$1 pow 2 = (p:real^3)$1 pow 2 + p$3 pow 2` THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let MOI_S3CL_REV_SUPER = prove
 (`!x:real^3->bool. x SUBSET {q:real^3 | q$3 = &0 /\ &0 < q$1} ==> x SUBSET revolution x`,
  GEN_TAC THEN REWRITE_TAC[SUBSET; revolution; IN_ELIM_THM] THEN DISCH_TAC THEN
  X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN EXISTS_TAC `p:real^3` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_ADD_RID] THEN ASM_REAL_ARITH_TAC);;

(* A connected set missing the sphere of radius r stays on one side of it.  *)

let MOI_S3CL_CONN_NORM = prove
 (`!(s:real^N->bool) a r.
     connected s /\ a IN s /\ &0 < r /\ DISJOINT s (sphere(vec 0,r))
     ==> (norm a < r ==> !x. x IN s ==> norm x < r) /\
         (r < norm a ==> !x. x IN s ==> r < norm x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `ball(vec 0:real^N,r)`] CONNECTED_INTER_FRONTIER) THEN
    ASM_SIMP_TAC[FRONTIER_BALL] THEN
    UNDISCH_TAC `DISJOINT (s:real^N->bool) (sphere(vec 0,r))` THEN
    UNDISCH_TAC `norm(a:real^N) < r` THEN UNDISCH_TAC `(a:real^N) IN s` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_DIFF; NOT_IN_EMPTY; IN_BALL_0] THEN
    MESON_TAC[];
    MP_TAC(ISPECL [`s:real^N->bool`; `cball(vec 0:real^N,r)`] CONNECTED_INTER_FRONTIER) THEN
    ASM_REWRITE_TAC[FRONTIER_CBALL] THEN
    UNDISCH_TAC `DISJOINT (s:real^N->bool) (sphere(vec 0,r))` THEN
    UNDISCH_TAC `r < norm(a:real^N)` THEN UNDISCH_TAC `(a:real^N) IN s` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_DIFF; NOT_IN_EMPTY; IN_CBALL_0] THEN
    MESON_TAC[REAL_NOT_LE]]);;

let MOI_S3CL_RIM_NORM = prove
 (`!x:real^3. x IN moi_s32_rim ==> norm x = &1`,
  REWRITE_TAC[moi_s32_rim; moi_s32_disk; IN_ELIM_THM; NORM_EQ_1; DOT_3] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x:real^3)$1 pow 2 + x$3 pow 2 = &1` THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let MOI_S3CL_SPHERE_FIN = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_tower g v pp dd s2
     ==> !r. &0 < r /\ r < &1
             ==> FINITE {i:int | ~(revolution (dd i) INTER sphere(vec 0,r) = {})}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_tower] THEN
  DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN DISCH_TAC THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[COMPACT_SPHERE; DISJOINT; EXTENSION; IN_INTER; IN_INSERT; NOT_IN_EMPTY;
              IN_SPHERE_0] THEN
  X_GEN_TAC `x:real^3` THEN
  ASM_CASES_TAC `x:real^3 = vec 0` THEN ASM_REWRITE_TAC[NORM_0] THENL
   [ASM_REAL_ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (ASSUME_TAC o MATCH_MP MOI_S3CL_RIM_NORM)) THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_S3CL_FINITE_INT_LB = prove
 (`!s:int->bool. FINITE s ==> ?b. !i. i IN s ==> b <= i`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY] THEN MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `s:int->bool`] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:int` o CONJUNCT1) THEN
  EXISTS_TAC `min x b:int` THEN REWRITE_TAC[IN_INSERT] THEN X_GEN_TAC `i:int` THEN
  STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `i:int`) THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

let MOI_S3CL_FIN_NBHD = prove
 (`!s:int->bool. FINITE s ==> FINITE {m:int | ?j. j IN s /\ m - &1 <= j /\ j <= m + &1}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\j:int. j - &1) s UNION s UNION IMAGE (\j:int. j + &1) s` THEN
  ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; IN_IMAGE] THEN
  X_GEN_TAC `m:int` THEN DISCH_THEN(X_CHOOSE_THEN `j:int` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `m = j + &1 \/ m = j \/ m = j - &1:int` STRIP_ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC;
    DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `j:int` THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[];
    DISJ1_TAC THEN EXISTS_TAC `j:int` THEN ASM_REWRITE_TAC[]]);;

(* The low end: the revolved cells with small index lie in small balls.    *)

let MOI_S3CL_TOWER_LOW = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_tower g v pp dd s2
     ==> !d. &0 < d ==> ?J. !j. j <= J ==> revolution (dd j) SUBSET ball(vec 0,d)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 (LABEL_TAC "pp") (LABEL_TAC "mono") o
              MATCH_MP MOI_S3CL_PP_FACTS) THEN
  FIRST_ASSUM(LABEL_TAC "dd" o MATCH_MP MOI_S3CL_DD_FACTS) THEN
  SUBGOAL_THEN `?rho. &0 < rho /\ rho < &1 /\ rho <= d` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min d (&1 / &2)` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `rho:real` o MATCH_MP MOI_S3CL_SPHERE_FIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:int` (LABEL_TAC "b") o MATCH_MP MOI_S3CL_FINITE_INT_LB) THEN
  SUBGOAL_THEN `?i0:int. ((pp:int->real^3) i0)$1 < rho` (X_CHOOSE_TAC `i0:int`) THENL
   [UNDISCH_TAC `moi_s32_tower (g:real^3->real^3) v pp dd s2` THEN
    REWRITE_TAC[moi_s32_tower] THEN
    DISCH_THEN(MP_TAC o SPEC `rho:real` o el 3 o CONJUNCTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `min (b - &1) i0:int` THEN X_GEN_TAC `j:int` THEN DISCH_TAC THEN
  SUBGOAL_THEN `revolution ((dd:int->real^3->bool) j) INTER sphere(vec 0,rho) = {}`
  ASSUME_TAC THENL
   [USE_THEN "b" (MP_TAC o SPEC `j:int`) THEN REWRITE_TAC[IN_ELIM_THM] THEN
    UNDISCH_TAC `j <= min (b - &1) i0:int` THEN
    MESON_TAC[INT_ARITH `j <= min (b - &1) i0 ==> ~(b <= j:int)`];
    ALL_TAC] THEN
  USE_THEN "dd" (STRIP_ASSUME_TAC o SPEC `j:int`) THEN
  SUBGOAL_THEN `(dd:int->real^3->bool) j SUBSET revolution (dd j)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3CL_REV_SUPER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `norm((pp:int->real^3) j) < rho` ASSUME_TAC THENL
   [USE_THEN "pp" (fun th -> REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC `j:int` th))]) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `((pp:int->real^3) i0)$1` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "mono" MATCH_MP_TAC THEN
    UNDISCH_TAC `j <= min (b - &1) i0:int` THEN REWRITE_TAC[INT_LE_MIN] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(dd:int->real^3->bool) j`; `(pp:int->real^3) j`; `rho:real`]
    MOI_S3CL_CONN_NORM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(dd:int->real^3->bool) j SUBSET revolution (dd j)` THEN
    UNDISCH_TAC `revolution ((dd:int->real^3->bool) j) INTER sphere(vec 0,rho) = {}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C MP (ASSUME `norm((pp:int->real^3) j) < rho`) o CONJUNCT1) THEN
  DISCH_TAC THEN REWRITE_TAC[SUBSET; IN_BALL_0] THEN X_GEN_TAC `p:real^3` THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC o MATCH_MP MOI_S3CL_REV_NORM) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `rho:real` THEN
  ASM_SIMP_TAC[]);;

(* The far end: the revolved cells from index K on stay off a ball at 0.    *)

let MOI_S3CL_TOWER_FAR = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_tower g v pp dd s2
     ==> !K. ?r. &0 < r /\ !j. K <= j ==> DISJOINT (revolution (dd j)) (ball(vec 0,r))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `K:int` THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 (LABEL_TAC "pp") (LABEL_TAC "mono") o
              MATCH_MP MOI_S3CL_PP_FACTS) THEN
  FIRST_ASSUM(LABEL_TAC "dd" o MATCH_MP MOI_S3CL_DD_FACTS) THEN
  SUBGOAL_THEN `?rho. &0 < rho /\ rho < &1 /\ rho < ((pp:int->real^3) K)$1`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `((pp:int->real^3) K)$1 / &2` THEN
    USE_THEN "pp" (MP_TAC o SPEC `K:int`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `rho:real` o MATCH_MP MOI_S3CL_SPHERE_FIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?r1. &0 < r1 /\
         !i q. i IN {i:int | ~(revolution ((dd:int->real^3->bool) i) INTER
                               sphere(vec 0,rho) = {})} /\ q IN dd i
               ==> r1 <= norm q`
  (X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r1"))) THENL
   [MP_TAC(ISPECL [`UNIONS (IMAGE (dd:int->real^3->bool)
                      {i:int | ~(revolution (dd i) INTER sphere(vec 0,rho) = {})})`;
                   `vec 0:real^3`] SEPARATE_POINT_CLOSED) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_UNIONS THEN
        ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
        X_GEN_TAC `i:int` THEN DISCH_TAC THEN USE_THEN "dd" (MP_TAC o SPEC `i:int`) THEN
        SIMP_TAC[];
        REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `i:int` (MP_TAC o CONJUNCT2)) THEN
        USE_THEN "dd" (MP_TAC o CONJUNCT1 o SPEC `i:int`) THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
        REWRITE_TAC[VEC_COMPONENT] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r1:real` THEN
      REWRITE_TAC[DIST_0] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `min rho r1` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `j:int` THEN DISCH_TAC THEN
  USE_THEN "dd" (STRIP_ASSUME_TAC o SPEC `j:int`) THEN
  SUBGOAL_THEN `!q. q IN (dd:int->real^3->bool) j ==> min rho r1 <= norm q`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `revolution ((dd:int->real^3->bool) j) INTER sphere(vec 0,rho) = {}`
    THENL
     [SUBGOAL_THEN `(dd:int->real^3->bool) j SUBSET revolution (dd j)` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_S3CL_REV_SUPER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `rho < norm((pp:int->real^3) j)` ASSUME_TAC THENL
       [USE_THEN "pp" (fun th -> REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC `j:int` th))]) THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `((pp:int->real^3) K)$1` THEN
        ASM_REWRITE_TAC[] THEN USE_THEN "mono" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`(dd:int->real^3->bool) j`; `(pp:int->real^3) j`; `rho:real`]
        MOI_S3CL_CONN_NORM) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(dd:int->real^3->bool) j SUBSET revolution (dd j)` THEN
        UNDISCH_TAC `revolution ((dd:int->real^3->bool) j) INTER sphere(vec 0,rho) = {}` THEN
        SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o C MP (ASSUME `rho < norm((pp:int->real^3) j)`) o CONJUNCT2) THEN
      DISCH_TAC THEN X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `q:real^3`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `r1:real` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "r1" MATCH_MP_TAC THEN EXISTS_TAC `j:int` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_BALL_0] THEN
  X_GEN_TAC `p:real^3` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC o MATCH_MP MOI_S3CL_REV_NORM) THEN
  SUBGOAL_THEN `min rho r1 <= norm(q:real^3)` MP_TAC THENL
   [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC]);;

(* Local finiteness inside v.                                               *)

let MOI_S3CL_TOWER_LF = prove
 (`!(g:real^3->real^3) v pp dd s2.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> !y. y IN v
             ==> ?r. &0 < r /\ ball(y,r) SUBSET v /\
                     FINITE {i:int | ~(revolution (dd i) INTER ball(y,r) = {})}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  UNDISCH_TAC `moi_s32_model (g:real^3->real^3) v` THEN REWRITE_TAC[moi_s32_model] THEN
  STRIP_TAC THEN
  MP_TAC MOI_S3GF_MODEL_POINTS THEN STRIP_TAC THEN
  MP_TAC MOI_S3GF_CYL_PARTS THEN STRIP_TAC THEN
  UNDISCH_TAC `open(v:real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{i:int | ~(revolution ((dd:int->real^3->bool) i) INTER cball(y,e) = {})}` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `moi_s32_tower (g:real^3->real^3) v pp dd s2` THEN
    REWRITE_TAC[moi_s32_tower] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    REWRITE_TAC[COMPACT_CBALL] THEN
    UNDISCH_TAC `cball(y:real^3,e) SUBSET v` THEN
    UNDISCH_TAC `DISJOINT (v:real^3->bool) moi_s32_axis` THEN
    UNDISCH_TAC `(v:real^3->bool) SUBSET interior moi_s32_cyl` THEN
    UNDISCH_TAC `vec 0 IN moi_s32_axis` THEN
    UNDISCH_TAC `moi_s32_rim SUBSET frontier moi_s32_cyl` THEN
    UNDISCH_TAC `frontier moi_s32_cyl INTER interior moi_s32_cyl = {}` THEN
    SET_TAC[];
    MP_TAC(ISPECL [`y:real^3`; `e:real`] BALL_SUBSET_CBALL) THEN SET_TAC[]]);;

(* Small balls at the centre lie in the model interior.                    *)

let MOI_S3CL_BALL_CYL = prove
 (`!r. r <= &1 / &2 ==> ball(vec 0:real^3,r) SUBSET interior moi_s32_cyl`,
  REWRITE_TAC[MOI_S3GF_INTERIOR_CYL; SUBSET; IN_BALL_0; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THENL
   [MP_TAC(SPECL [`2`; `norm(x:real^3)`] REAL_POW_1_LT) THEN
    MP_TAC(ISPEC `x:real^3` NORM_POW_2) THEN MP_TAC(ISPEC `x:real^3` NORM_POS_LE) THEN
    MP_TAC(SPEC `(x:real^3)$2` REAL_LE_SQUARE) THEN
    REWRITE_TAC[DOT_3; REAL_POW_2; ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`x:real^3`; `2`] COMPONENT_LE_NORM) THEN ASM_REAL_ARITH_TAC]);;
(* ------------------------------------------------------------------------- *)
(* The two ends and local finiteness of the chain in R^3, through g.        *)
(* ------------------------------------------------------------------------- *)

(* Each annulus A(k) lies in the revolved cells of index k - 1 .. k + 1.    *)

let MOI_S3CL_ANN_LVL = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> !k x. x IN moi_s3cl_ann hh bb k
               ==> ?j. k - &1 <= j /\ j <= k + &1 /\ x IN IMAGE g (revolution (dd j))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3GF_CHAIN_PIECES) THEN
  DISCH_THEN(LABEL_TAC "h" o CONJUNCT1) THEN
  SUBGOAL_THEN `!i. (bb:int->real^3->bool) i SUBSET moi_s32_lvl g dd i` (LABEL_TAC "b")
  THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN REWRITE_TAC[moi_s32_chain] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3CL_INT_CASES THEN REWRITE_TAC[MOI_S3CL_ANN_CIRC] THEN
  CONJ_TAC THEN X_GEN_TAC `i:int` THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THENL
   [EXISTS_TAC `&2 * i:int` THEN REPEAT CONJ_TAC THENL
     [INT_ARITH_TAC; INT_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "h" (MP_TAC o SPEC `i:int`) THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[];
    USE_THEN "b" (MP_TAC o SPEC `i:int`) THEN REWRITE_TAC[moi_s32_lvl] THEN
    REWRITE_TAC[SUBSET; IN_UNION] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [EXISTS_TAC `&2 * i:int`; EXISTS_TAC `&2 * i + &1:int`; EXISTS_TAC `&2 * i + &2:int`] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

(* Points of g(rev dd(j)) that g maps from a set u inside the model come    *)
(* from rev dd(j) INTER u.                                                   *)

let MOI_S3CL_IMAGE_MEET = prove
 (`!(g:real^3->real^3) v pp dd s2 j u z.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\ u SUBSET moi_s32_cyl /\
     z IN IMAGE g (revolution (dd j)) /\ z IN IMAGE g u
     ==> ?p. p IN revolution (dd j) /\ p IN u /\ z = g p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3CL_REV_CYL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2 o SPEC `j:int`) THEN DISCH_TAC THEN
  UNDISCH_TAC `moi_s32_model (g:real^3->real^3) v` THEN REWRITE_TAC[moi_s32_model] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN DISCH_TAC THEN
  UNDISCH_TAC `(z:real^3) IN IMAGE (g:real^3->real^3) u` THEN
  UNDISCH_TAC `(z:real^3) IN IMAGE (g:real^3->real^3) (revolution (dd (j:int)))` THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `p':real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `p:real^3 = p'` (fun th -> ASM_REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* g maps open subsets of the model interior to open sets.                 *)

let MOI_S3CL_G_OPEN = prove
 (`!(g:real^3->real^3) v u.
     moi_s32_model g v /\ open u /\ u SUBSET interior moi_s32_cyl ==> open (IMAGE g u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_model] THEN STRIP_TAC THEN
  MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(u:real^3->bool) SUBSET moi_s32_cyl` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s32_cyl` THEN
    ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

(* (lf) The annuli are locally finite at their points.                     *)

let MOI_S3CL_AA_LF = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> !k x. x IN moi_s3cl_ann hh bb k
               ==> ?u. open u /\ x IN u /\
                       FINITE {m:int | ~(moi_s3cl_ann hh bb m INTER u = {})}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "lvl" o MATCH_MP MOI_S3CL_ANN_LVL) THEN
  FIRST_ASSUM(LABEL_TAC "c0" o MATCH_MP MOI_S3CL_AA_C0) THEN
  FIRST_ASSUM(fun th -> LABEL_TAC "lf" (MATCH_MP MOI_S3CL_TOWER_LF
    (CONJ (CONJUNCT1 th) (CONJUNCT1(CONJUNCT2 th))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s32_model] o CONJUNCT1) THEN
  MAP_EVERY X_GEN_TAC [`k:int`; `x:real^3`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?y. y IN v /\ x = (g:real^3->real^3) y` STRIP_ASSUME_TAC THENL
   [USE_THEN "c0" (MP_TAC o CONJUNCT1 o SPEC `k:int`) THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "lf" (MP_TAC o C MP (ASSUME `(y:real^3) IN v`) o SPEC `y:real^3`) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ball(y:real^3,r) SUBSET moi_s32_cyl` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (g:real^3->real^3) (ball(y,r))` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3CL_G_OPEN THEN EXISTS_TAC `v:real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN ASM_MESON_TAC[SUBSET_TRANS];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{m:int | ?j. j IN {i:int | ~(revolution ((dd:int->real^3->bool) i) INTER
                                             ball(y,r) = {})} /\
                           m - &1 <= j /\ j <= m + &1}` THEN
  CONJ_TAC THENL [MATCH_MP_TAC MOI_S3CL_FIN_NBHD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `m:int` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "lvl" (MP_TAC o C MP (ASSUME `(z:real^3) IN moi_s3cl_ann hh bb m`) o
                  SPECL [`m:int`; `z:real^3`]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j:int` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `j:int`;
                `ball(y:real^3,r)`; `z:real^3`] MOI_S3CL_IMAGE_MEET) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* (low) The annuli of small index lie in small balls at g 0.              *)

let MOI_S3CL_AA_LOW = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> !e. &0 < e ==> ?K. !k. k <= K ==> moi_s3cl_ann hh bb k SUBSET ball(g (vec 0),e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "lvl" o MATCH_MP MOI_S3CL_ANN_LVL) THEN
  FIRST_ASSUM(fun th -> LABEL_TAC "rc" (MATCH_MP MOI_S3CL_REV_CYL
    (CONJ (CONJUNCT1 th) (CONJUNCT1(CONJUNCT2 th))))) THEN
  FIRST_ASSUM(LABEL_TAC "low" o MATCH_MP MOI_S3CL_TOWER_LOW o CONJUNCT1 o CONJUNCT2) THEN
  SUBGOAL_THEN `(g:real^3->real^3) continuous at (vec 0)` MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_INTERIOR THEN EXISTS_TAC `moi_s32_cyl` THEN
    REWRITE_TAC[MOI_S3GF_MODEL_POINTS] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [moi_s32_model] o CONJUNCT1) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[DIST_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "low" (MP_TAC o C MP (ASSUME `&0 < d`) o SPEC `d:real`) THEN
  DISCH_THEN(X_CHOOSE_TAC `J:int`) THEN EXISTS_TAC `J - &1:int` THEN
  X_GEN_TAC `k:int` THEN DISCH_TAC THEN REWRITE_TAC[SUBSET] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  USE_THEN "lvl" (MP_TAC o C MP (ASSUME `(z:real^3) IN moi_s3cl_ann hh bb k`) o
                  SPECL [`k:int`; `z:real^3`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:int` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(z:real^3) IN IMAGE (g:real^3->real^3) (revolution (dd (j:int)))` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `revolution ((dd:int->real^3->bool) j) SUBSET ball(vec 0,d)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_INT_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* (far) From index K on, the annuli stay off a ball at g 0.               *)

let MOI_S3CL_AA_FAR = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> !K. ?e. &0 < e /\
                 !k. K <= k ==> DISJOINT (moi_s3cl_ann hh bb k) (ball(g (vec 0),e))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `K:int` THEN
  FIRST_ASSUM(LABEL_TAC "lvl" o MATCH_MP MOI_S3CL_ANN_LVL) THEN
  FIRST_ASSUM(MP_TAC o SPEC `K - &1:int` o MATCH_MP MOI_S3CL_TOWER_FAR o
              CONJUNCT1 o CONJUNCT2) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "far"))) THEN
  SUBGOAL_THEN `open (IMAGE (g:real^3->real^3) (ball(vec 0,min r (&1 / &2))))` MP_TAC THENL
   [MATCH_MP_TAC MOI_S3CL_G_OPEN THEN EXISTS_TAC `v:real^3->bool` THEN
    REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1);
      MATCH_MP_TAC MOI_S3CL_BALL_CYL THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `(g:real^3->real^3) (vec 0)`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:int` THEN DISCH_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  USE_THEN "lvl" (MP_TAC o C MP (ASSUME `(z:real^3) IN moi_s3cl_ann hh bb k`) o
                  SPECL [`k:int`; `z:real^3`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:int` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`; `j:int`;
                `ball(vec 0:real^3,min r (&1 / &2))`; `z:real^3`] MOI_S3CL_IMAGE_MEET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interior moi_s32_cyl` THEN
      REWRITE_TAC[INTERIOR_SUBSET] THEN MATCH_MP_TAC MOI_S3CL_BALL_CYL THEN
      REAL_ARITH_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "far" (MP_TAC o SPEC `j:int`) THEN ANTS_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(p:real^3) IN ball(vec 0,min r (&1 / &2))` THEN
  REWRITE_TAC[IN_BALL_0] THEN REAL_ARITH_TAC);;

(* The chain set is an open disk.                                           *)

let MOI_S3CL_CHAINSET_DISK = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> moi_s32_chainset g hh bb homeomorphic ball(vec 0:real^2,&1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_s32_chainset (g:real^3->real^3) hh bb =
                g (vec 0) INSERT UNIONS {moi_s3cl_ann hh bb k | k IN (:int)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_s32_chainset; MOI_S3CL_UNIONS_ANN] THEN SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3CL_CHAIN_DISK THEN EXISTS_TAC `moi_s3cl_circ jl jh` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP MOI_S3CL_AA_PARAM o CONJUNCT2 o CONJUNCT2);
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_S3CL_AA_INT);
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_S3CL_AA_DIS);
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3CL_AA_C0) THEN SIMP_TAC[];
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_S3CL_AA_LF);
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_S3CL_AA_LOW);
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_S3CL_AA_FAR)]);;

(* ------------------------------------------------------------------------- *)
(* Part 6. The rim circle, local polyhedrality, and the closure of the     *)
(* chain (both inclusions; the second from the separation in M).           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Part 6a. The rim is a circle; the annuli are polyhedra; the chain minus   *)
(* the centre is locally polyhedral.                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CL_RIM_IMAGE = prove
 (`moi_s32_rim = IMAGE (\z:real^2. vector[z$1; &0; z$2]:real^3) (sphere(vec 0,&1))`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; moi_s32_rim; moi_s32_disk; moi_s32_cyl; IN_ELIM_THM;
              IN_SPHERE_0; NORM_EQ_1; DOT_2] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `vector[(x:real^3)$1; x$3]:real^2` THEN
    REWRITE_TAC[VECTOR_2; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^3)$1 pow 2 + x$3 pow 2 = &1` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[VECTOR_3] THEN
    UNDISCH_TAC `(z:real^2)$1 * z$1 + z$2 * z$2 = &1` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;

let MOI_S3CL_RIM_CIRCLE = prove
 (`compact moi_s32_rim /\ moi_s32_rim homeomorphic sphere(vec 0:real^2,&1)`,
  SUBGOAL_THEN `linear (\z:real^2. vector[z$1; &0; z$2]:real^3) /\
                (!x y. (\z:real^2. vector[z$1; &0; z$2]:real^3) x =
                       (\z:real^2. vector[z$1; &0; z$2]:real^3) y ==> x = y)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3; VECTOR_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MOI_S3CL_RIM_IMAGE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN ASM_REWRITE_TAC[COMPACT_SPHERE];
    MATCH_MP_TAC HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF THEN ASM_REWRITE_TAC[]]);;

let MOI_S3CL_GRIM_CIRCLE = prove
 (`!(g:real^3->real^3) v.
     moi_s32_model g v ==> IMAGE g moi_s32_rim homeomorphic sphere(vec 0:real^2,&1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_model] THEN STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] HOMEOMORPHIC_TRANS) THEN EXISTS_TAC `moi_s32_rim` THEN
  REWRITE_TAC[MOI_S3CL_RIM_CIRCLE] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  REWRITE_TAC[homeomorphic] THEN EXISTS_TAC `g:real^3->real^3` THEN
  MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN REWRITE_TAC[MOI_S3CL_RIM_CIRCLE] THEN
  SUBGOAL_THEN `moi_s32_rim SUBSET moi_s32_cyl` ASSUME_TAC THENL
   [MP_TAC MOI_STD_S32_MODEL_FACTS THEN SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]]);;

(* The square annulus is a union of four rectangles, so a PL annulus is a   *)
(* polyhedron (PL_POLYHEDRON_PL_IMAGE).                                      *)

let MOI_S3CL_SQ_POLYHEDRON = prove
 (`pl_polyhedron (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
                  interval(--vector[&1;&1],vector[&1;&1]))`,
  REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `{interval[vector[-- &2;-- &2]:real^2,vector[-- &1;&2]],
               interval[vector[&1;-- &2]:real^2,vector[&2;&2]],
               interval[vector[-- &1;-- &2]:real^2,vector[&1;-- &1]],
               interval[vector[-- &1;&1]:real^2,vector[&1;&2]]}` THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
              POLYTOPE_INTERVAL; UNIONS_INSERT; UNIONS_0; UNION_EMPTY] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNION; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_NEG_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_S3CL_ANNULUS_POLYHEDRON = prove
 (`!(a:real^N->bool) j0 j1. pl_annulus_with_ends a j0 j1 ==> pl_polyhedron a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_annulus_with_ends; pl_homeomorphism; homeomorphism] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `a:real^N->bool`
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[MOI_S3CL_SQ_POLYHEDRON]);;

let MOI_S3CL_AA_POLYHEDRON = prove
 (`!(g:real^3->real^3) dd s2 hh bb jl jh.
     moi_s32_chain g dd s2 hh bb jl jh ==> !k. pl_polyhedron (moi_s3cl_ann hh bb k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_chain] THEN
  DISCH_THEN(LABEL_TAC "c" o CONJUNCT1) THEN MATCH_MP_TAC MOI_S3CL_INT_CASES THEN
  REWRITE_TAC[MOI_S3CL_ANN_CIRC] THEN CONJ_TAC THEN X_GEN_TAC `i:int` THEN
  MATCH_MP_TAC MOI_S3CL_ANNULUS_POLYHEDRON THEN
  USE_THEN "c" (STRIP_ASSUME_TAC o SPEC `i:int`) THEN ASM_MESON_TAC[]);;

(* The chain minus its centre: the union of the annuli; locally polyhedral. *)

let MOI_S3CL_CHAINSET_DELETE = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> moi_s32_chainset g hh bb DELETE g (vec 0) =
         UNIONS {moi_s3cl_ann hh bb k | k IN (:int)}`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_S3CL_AA_C0) THEN
  REWRITE_TAC[moi_s32_chainset; GSYM MOI_S3CL_UNIONS_ANN] THEN
  REWRITE_TAC[EXTENSION; IN_DELETE; IN_UNION; IN_UNIONS; IN_ELIM_THM; IN_UNIV; IN_SING] THEN
  MESON_TAC[]);;

let MOI_S3CL_LOCALLY_POLY = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> locally_polyhedral (moi_s32_chainset g hh bb DELETE g (vec 0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP MOI_S3CL_CHAINSET_DELETE) THEN
  FIRST_ASSUM(LABEL_TAC "lf" o MATCH_MP MOI_S3CL_AA_LF) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3CL_AA_POLYHEDRON o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[pl_polyhedron; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:int->(real^3->bool)->bool`
    (LABEL_TAC "cc" o ONCE_REWRITE_RULE[EQ_SYM_EQ])) THEN
  REWRITE_TAC[locally_polyhedral; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
  X_GEN_TAC `x:real^3` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:int` SUBST_ALL_TAC) o ONCE_REWRITE_RULE[CONJ_SYM])) THEN
  USE_THEN "lf" (MP_TAC o C MP (ASSUME `(x:real^3) IN moi_s3cl_ann hh bb k`) o
                 SPECL [`k:int`; `x:real^3`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `UNIONS (IMAGE (cc:int->(real^3->bool)->bool)
                 {m:int | ~(moi_s3cl_ann hh bb m INTER u = {})})` THEN
  EXISTS_TAC `u:real^3->bool` THEN
  REWRITE_TAC[ASSUME `open(u:real^3->bool)`; ASSUME `(x:real^3) IN u`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[FORALL_IN_IMAGE] THEN USE_THEN "cc" (fun th -> REWRITE_TAC[th])];
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM; IN_UNIV; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t':real^3->bool` (CONJUNCTS_THEN2
      ASSUME_TAC (X_CHOOSE_THEN `m:int` SUBST_ALL_TAC) o ONCE_REWRITE_RULE[CONJ_SYM]))
      ASSUME_TAC) THEN
    USE_THEN "cc" (MP_TAC o CONJUNCT2 o CONJUNCT2 o SPEC `m:int`) THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS] THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
    REWRITE_TAC[ASSUME `(z:real^3) IN moi_s3cl_ann hh bb m`] THEN
    DISCH_THEN(X_CHOOSE_THEN `tt:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `tt:real^3->bool` THEN REWRITE_TAC[ASSUME `(z:real^3) IN tt`] THEN
    EXISTS_TAC `m:int` THEN REWRITE_TAC[ASSUME `(tt:real^3->bool) IN cc (m:int)`] THEN
    UNDISCH_TAC `(z:real^3) IN moi_s3cl_ann hh bb m` THEN UNDISCH_TAC `(z:real^3) IN u` THEN
    SET_TAC[];
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `p:real^3->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `m:int` STRIP_ASSUME_TAC) THEN
    USE_THEN "cc" (MP_TAC o SPEC `m:int`) THEN STRIP_TAC THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    EXISTS_TAC `moi_s3cl_ann hh bb m` THEN CONJ_TAC THENL
     [EXISTS_TAC `m:int` THEN REFL_TAC;
      UNDISCH_TAC `UNIONS ((cc:int->(real^3->bool)->bool) m) = moi_s3cl_ann hh bb m` THEN
      UNDISCH_TAC `(p:real^3->bool) IN cc (m:int)` THEN UNDISCH_TAC `(y:real^3) IN p` THEN
      SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 6b. The closure of the chain, first inclusion: closure X SUBSET      *)
(* X UNION g(rim).  We work with the preimage W = g^-1(X) in the model.      *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CL_CLOSURE_IMAGE = prove
 (`!(g:real^3->real^3) v s.
     moi_s32_model g v /\ s SUBSET moi_s32_cyl
     ==> closure s SUBSET moi_s32_cyl /\ closure (IMAGE g s) = IMAGE g (closure s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_model] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closure s SUBSET moi_s32_cyl` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[MOI_S3GF_CYL_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3) continuous_on closure s` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[CLOSURE_SUBSET];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[COMPACT_CLOSURE] THEN
      ASM_MESON_TAC[BOUNDED_SUBSET; MOI_S3GF_CYL_BOUNDED]];
    MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN
    ASM_REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET]]);;

let MOI_S3CL_W_IMAGE = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> IMAGE g {x | x IN moi_s32_cyl /\ g x IN moi_s32_chainset g hh bb} =
         moi_s32_chainset g hh bb`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MOI_S3GF_CHAIN_OPEN) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MOI_S3GF_MODEL_OPEN o CONJUNCT1) THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC MOI_S3GF_CYL_PARTS THEN SET_TAC[]);;

(* Points of the closure of W in the model interior lie in W.               *)

let MOI_S3CL_W_INTERIOR = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh q.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh /\
     q IN interior moi_s32_cyl /\
     q IN closure {x | x IN moi_s32_cyl /\ g x IN moi_s32_chainset g hh bb}
     ==> g q IN moi_s32_chainset g hh bb`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `?t. closed t /\ IMAGE (g:real^3->real^3) (interior moi_s32_cyl) INTER t =
                    moi_s32_chainset g hh bb`
  (X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THENL
   [ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[GSYM CLOSED_IN_CLOSED] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o CONJUNCT1 o MATCH_MP MOI_S3GF_MODEL_OPEN) THEN
    UNDISCH_TAC `moi_s32_chain (g:real^3->real^3) dd s2 hh bb jl jh` THEN
    REWRITE_TAC[moi_s32_chain] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`;
     `{x | x IN moi_s32_cyl /\ (g:real^3->real^3) x IN moi_s32_chainset g hh bb}`]
    MOI_S3CL_CLOSURE_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `closure (IMAGE (g:real^3->real^3)
                   {x | x IN moi_s32_cyl /\ g x IN moi_s32_chainset g hh bb}) SUBSET t`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (g:real^3->real^3) (interior moi_s32_cyl) INTER t =
                   moi_s32_chainset g hh bb` THEN SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3) q IN t` ASSUME_TAC THENL
   [UNDISCH_TAC `closure (IMAGE (g:real^3->real^3)
                   {x | x IN moi_s32_cyl /\ g x IN moi_s32_chainset g hh bb}) SUBSET t` THEN
    UNDISCH_TAC `closure (IMAGE (g:real^3->real^3)
                   {x | x IN moi_s32_cyl /\ g x IN moi_s32_chainset g hh bb}) =
                 IMAGE g (closure {x | x IN moi_s32_cyl /\ g x IN moi_s32_chainset g hh bb})` THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `(q:real^3) IN closure {x | x IN moi_s32_cyl /\
                    (g:real^3->real^3) x IN moi_s32_chainset g hh bb}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (g:real^3->real^3) (interior moi_s32_cyl) INTER t =
               moi_s32_chainset g hh bb` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC]);;

(* The preimages of the annuli are closed and lie in v.                     *)

let MOI_S3CL_WK_CLOSED = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> !k. closed {x | x IN moi_s32_cyl /\ g x IN moi_s3cl_ann hh bb k} /\
             {x | x IN moi_s32_cyl /\ g x IN moi_s3cl_ann hh bb k} SUBSET v`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "c0" o MATCH_MP MOI_S3CL_AA_C0) THEN
  FIRST_ASSUM(LABEL_TAC "par" o MATCH_MP MOI_S3CL_AA_PARAM o CONJUNCT2 o CONJUNCT2) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s32_model] o CONJUNCT1) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gc") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
    STRIP_ASSUME_TAC)) THEN
  X_GEN_TAC `k:int` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
    USE_THEN "gc" (fun th -> REWRITE_TAC[th; MOI_S3GF_CYL_CLOSED]) THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    USE_THEN "par" (X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_THEN `f':real^3->real^2`
      (MP_TAC o CONJUNCT1)) o SPEC `k:int`) THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rhs(concl th) = `moi_s3cl_ann hh bb k`
                            then SUBST1_TAC(SYM th) else NO_TAC) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[MOI_S3CL_SANN_COMPACT];
    USE_THEN "c0" (MP_TAC o CONJUNCT1 o SPEC `k:int`) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN DISCH_TAC THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(g:real^3->real^3) x`) THEN
    REWRITE_TAC[ASSUME `(g:real^3->real^3) x IN moi_s3cl_ann hh bb k`] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `x:real^3 = y` (fun th -> ASM_REWRITE_TAC[th]) THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET]]);;

(* Points of the model frontier off the rim are not in the closure of W:   *)
(* a compact neighbourhood off the centre and the rim meets finitely many   *)
(* revolved cells, hence finitely many closed preimages of annuli.          *)

let MOI_S3CL_W_FRONTIER = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh q.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh /\
     q IN moi_s32_cyl /\ ~(q IN interior moi_s32_cyl) /\ ~(q IN moi_s32_rim)
     ==> ~(q IN closure {x | x IN moi_s32_cyl /\ g x IN moi_s32_chainset g hh bb})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `moi_s32_model (g:real^3->real^3) v /\ moi_s32_tower g v pp dd s2 /\
                moi_s32_chain g dd s2 hh bb jl jh` (LABEL_TAC "H") THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "H" (LABEL_TAC "wk" o MATCH_MP MOI_S3CL_WK_CLOSED) THEN
  USE_THEN "H" (LABEL_TAC "lvl" o MATCH_MP MOI_S3CL_ANN_LVL) THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3CL_REV_CYL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "rc") THEN
  UNDISCH_TAC `moi_s32_model (g:real^3->real^3) v` THEN REWRITE_TAC[moi_s32_model] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gc") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
    STRIP_ASSUME_TAC)) THEN
  MP_TAC MOI_S3GF_MODEL_POINTS THEN STRIP_TAC THEN
  MP_TAC MOI_S3GF_CYL_PARTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(q:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s32_rim`; `q:real^3`] SEPARATE_POINT_CLOSED) THEN
  ASM_SIMP_TAC[MOI_S3CL_RIM_CIRCLE; COMPACT_IMP_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "e1"))) THEN
  SUBGOAL_THEN `?e. &0 < e /\ e < e1 /\ e < norm(q:real^3)` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min e1 (norm(q:real^3)) / &2` THEN
    UNDISCH_TAC `~(q:real^3 = vec 0)` THEN REWRITE_TAC[GSYM NORM_POS_LT] THEN
    UNDISCH_TAC `&0 < e1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the compact neighbourhood and the finitely many cells *)
  SUBGOAL_THEN `FINITE {j:int | ~(revolution ((dd:int->real^3->bool) j) INTER
                                  (cball(q,e) INTER moi_s32_cyl) = {})}` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_tower (g:real^3->real^3) v pp dd s2` THEN
    REWRITE_TAC[moi_s32_tower] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    SIMP_TAC[COMPACT_INTER_CLOSED; COMPACT_CBALL; MOI_S3GF_CYL_CLOSED] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_INSERT; NOT_IN_EMPTY; IN_CBALL] THEN
    X_GEN_TAC `x:real^3` THEN
    ASM_CASES_TAC `x:real^3 = vec 0` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[DIST_0] THEN MATCH_MP_TAC(TAUT `~p ==> ~(p /\ q)`) THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o CONJUNCT1) MP_TAC) THEN
      DISCH_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `e1 <= dist(q:real^3,x)` MP_TAC THENL
       [USE_THEN "e1" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?fk:int->bool. FINITE fk /\
                  !m z. z IN ball(q,e) /\ z IN moi_s32_cyl /\
                        (g:real^3->real^3) z IN moi_s3cl_ann hh bb m ==> m IN fk`
  (X_CHOOSE_THEN `fk:int->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fk"))) THENL
   [EXISTS_TAC `{m:int | ?j. j IN {j:int | ~(revolution ((dd:int->real^3->bool) j) INTER
                                    (cball(q,e) INTER moi_s32_cyl) = {})} /\
                             m - &1 <= j /\ j <= m + &1}` THEN
    CONJ_TAC THENL [MATCH_MP_TAC MOI_S3CL_FIN_NBHD THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`m:int`; `z:real^3`] THEN STRIP_TAC THEN
    USE_THEN "lvl" (MP_TAC o C MP (ASSUME `(g:real^3->real^3) z IN moi_s3cl_ann hh bb m`) o
                    SPECL [`m:int`; `(g:real^3->real^3) z`]) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:int` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `j:int` THEN
    REWRITE_TAC[ASSUME `m - &1 <= j:int`; ASSUME `j <= m + &1:int`] THEN
    UNDISCH_TAC `(g:real^3->real^3) z IN IMAGE g (revolution (dd (j:int)))` THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(p:real^3) IN moi_s32_cyl` ASSUME_TAC THENL
     [USE_THEN "rc" (MP_TAC o CONJUNCT2 o SPEC `j:int`) THEN
      UNDISCH_TAC `(p:real^3) IN revolution (dd (j:int))` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `z:real^3 = p` SUBST_ALL_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `p:real^3` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`q:real^3`; `e:real`] BALL_SUBSET_CBALL) THEN
    UNDISCH_TAC `(p:real^3) IN ball(q,e)` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the closed set Z *)
  SUBGOAL_THEN `closed (vec 0 INSERT UNIONS (IMAGE (\m. {x | x IN moi_s32_cyl /\
                  (g:real^3->real^3) x IN moi_s3cl_ann hh bb m}) fk))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_INSERT THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[FORALL_IN_IMAGE] THEN USE_THEN "wk" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(q:real^3,e) INTER
                {x | x IN moi_s32_cyl /\ (g:real^3->real^3) x IN moi_s32_chainset g hh bb}
                SUBSET vec 0 INSERT UNIONS (IMAGE (\m. {x | x IN moi_s32_cyl /\
                         g x IN moi_s3cl_ann hh bb m}) fk)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_INSERT; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    UNDISCH_TAC `(g:real^3->real^3) z IN moi_s32_chainset g hh bb` THEN
    REWRITE_TAC[moi_s32_chainset; GSYM MOI_S3CL_UNIONS_ANN; IN_UNION; IN_SING; IN_UNIONS;
                IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
      ASSUME_TAC (X_CHOOSE_THEN `k:int` SUBST_ALL_TAC) o ONCE_REWRITE_RULE[CONJ_SYM]))
      ASSUME_TAC) THENL
     [DISJ2_TAC THEN EXISTS_TAC `k:int` THEN
      REWRITE_TAC[ASSUME `(z:real^3) IN moi_s32_cyl`;
                  ASSUME `(g:real^3->real^3) z IN moi_s3cl_ann hh bb k`] THEN
      USE_THEN "fk" MATCH_MP_TAC THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
      DISJ1_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(q:real^3) IN ball(q,e)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(q:real^3,e)`;
     `{x | x IN moi_s32_cyl /\ (g:real^3->real^3) x IN moi_s32_chainset g hh bb}`]
    OPEN_INTER_CLOSURE_SUBSET) THEN
  REWRITE_TAC[OPEN_BALL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ball(q:real^3,e) INTER
                  {x | x IN moi_s32_cyl /\ (g:real^3->real^3) x IN moi_s32_chainset g hh bb}`;
                 `vec 0 INSERT UNIONS (IMAGE (\m. {x | x IN moi_s32_cyl /\
                    (g:real^3->real^3) x IN moi_s3cl_ann hh bb m}) fk)`] CLOSURE_MINIMAL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `(q:real^3) IN vec 0 INSERT UNIONS (IMAGE (\m. {x | x IN moi_s32_cyl /\
                  (g:real^3->real^3) x IN moi_s3cl_ann hh bb m}) fk)` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
  REWRITE_TAC[ASSUME `~(q:real^3 = vec 0)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:int` STRIP_ASSUME_TAC) THEN
  USE_THEN "wk" (MP_TAC o CONJUNCT2 o SPEC `m:int`) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `q:real^3`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `~((q:real^3) IN interior moi_s32_cyl)` THEN
  UNDISCH_TAC `(v:real^3->bool) SUBSET interior moi_s32_cyl` THEN
  UNDISCH_TAC `(q:real^3) IN v` THEN SET_TAC[]);;

let MOI_S3CL_W_CLOSURE = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> closure {x | x IN moi_s32_cyl /\ g x IN moi_s32_chainset g hh bb} SUBSET
         {x | x IN moi_s32_cyl /\ g x IN moi_s32_chainset g hh bb} UNION moi_s32_rim`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SUBSET; IN_UNION] THEN
  X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`;
     `{x | x IN moi_s32_cyl /\ (g:real^3->real^3) x IN moi_s32_chainset g hh bb}`]
    MOI_S3CL_CLOSURE_IMAGE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1); SET_TAC[]]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `(q:real^3) IN moi_s32_cyl` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(q:real^3) IN moi_s32_rim` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(q:real^3) IN interior moi_s32_cyl` THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S3CL_W_INTERIOR THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`;
                          `s2:int->real^3->bool`; `jl:int->real^3->bool`;
                          `jh:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                  `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                  `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`;
                  `q:real^3`] MOI_S3CL_W_FRONTIER) THEN
    ASM_REWRITE_TAC[]]);;

(* First inclusion in R^3.                                                  *)

let MOI_S3CL_CLOSURE_SUB = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> closure (moi_s32_chainset g hh bb) SUBSET
         moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [SYM(MATCH_MP MOI_S3CL_W_IMAGE th)]) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`;
     `{x | x IN moi_s32_cyl /\ (g:real^3->real^3) x IN moi_s32_chainset g hh bb}`]
    MOI_S3CL_CLOSURE_IMAGE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1); SET_TAC[]]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3CL_W_CLOSURE) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3CL_W_IMAGE) THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 6c. The second inclusion: the rim lies in the closure, from the      *)
(* separation of g qlo from g qhi in M by the chain.  A rim point y0 off the *)
(* closure of W gives a path from qlo to qhi near the bottom face, the       *)
(* lateral segment through y0 and the top face, missing W.                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CL_SEP_CONN = prove
 (`!(m:real^N->bool) c s t k.
     separates_in m c s t /\ connected k /\ k SUBSET m DIFF c /\
     ~(k INTER s = {}) /\ ~(k INTER t = {}) ==> F`,
  REPEAT GEN_TAC THEN REWRITE_TAC[separates_in; OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `w:real^N->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `u1:real^N->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `w1:real^N->bool` STRIP_ASSUME_TAC)
        STRIP_ASSUME_TAC))))
    STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `connected(k:real^N->bool)` THEN
  REWRITE_TAC[connected; TAUT `(~p ==> F) <=> p`] THEN
  MAP_EVERY EXISTS_TAC [`u1:real^N->bool`; `w1:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S3CL_CONN_SEG_UNION = prove
 (`!(s:real^N->bool) a b. connected s /\ b IN s ==> connected (segment[a,b] UNION s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_UNION THEN
  ASM_REWRITE_TAC[CONNECTED_SEGMENT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  EXISTS_TAC `b:real^N` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT]);;

let MOI_S3CL_W_SUB = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> {x | x IN moi_s32_cyl /\ g x IN moi_s32_chainset g hh bb} SUBSET vec 0 INSERT v`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3GF_CHAIN_V) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s32_model] o CONJUNCT1) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "inj")
    STRIP_ASSUME_TAC)) THEN
  MP_TAC MOI_S3GF_MODEL_POINTS THEN STRIP_TAC THEN
  MP_TAC MOI_S3GF_CYL_PARTS THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; IN_IMAGE] THEN
  DISCH_TAC THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(g:real^3->real^3) x`) THEN
  REWRITE_TAC[ASSUME `(g:real^3->real^3) x IN moi_s32_chainset g hh bb`] THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISJ2_TAC THEN SUBGOAL_THEN `x:real^3 = x'` (fun th -> ASM_REWRITE_TAC[th]) THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* The compact set S of the bottom face, the top face and the lateral line  *)
(* through vector[a;0;b]; it lies in the model frontier and meets the rim   *)
(* only at that point.                                                       *)

let MOI_S3CL_SHADOW = prove
 (`!a b. a pow 2 + b pow 2 = &1
         ==> compact {x:real^3 | x IN moi_s32_cyl /\
                                 (x$2 = -- &1 \/ x$2 = &1 \/ x$1 = a /\ x$3 = b)} /\
             !x. x IN {x:real^3 | x IN moi_s32_cyl /\
                                  (x$2 = -- &1 \/ x$2 = &1 \/ x$1 = a /\ x$3 = b)}
                 ==> ~(x IN interior moi_s32_cyl) /\
                     (x IN moi_s32_rim ==> x = vector[a; &0; b])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `{x:real^3 | x IN moi_s32_cyl /\ (x$2 = -- &1 \/ x$2 = &1 \/ x$1 = a /\ x$3 = b)} =
      moi_s32_cyl INTER ({x | x$2 = -- &1} UNION {x | x$2 = &1} UNION
                         ({x | x$1 = a} INTER {x | x$3 = b}))` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_UNION]; ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
    SIMP_TAC[MOI_S3GF_CYL_COMPACT; CLOSED_UNION; CLOSED_INTER; CLOSED_STANDARD_HYPERPLANE];
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN CONJ_TAC THENL
     [REWRITE_TAC[MOI_S3GF_INTERIOR_CYL; IN_ELIM_THM] THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[moi_s32_rim; moi_s32_disk; IN_ELIM_THM] THEN STRIP_TAC THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
      UNDISCH_TAC `(x:real^3)$2 = -- &1 \/ x$2 = &1 \/ x$1 = a /\ x$3 = b` THEN
      ASM_REWRITE_TAC[REAL_ARITH `~(&0 = -- &1) /\ ~(&0 = &1)`] THEN SIMP_TAC[]]]);;

(* The five segments of the path.                                           *)

let MOI_S3CL_SEG_AX_LO = prove
 (`!eta x.
     &0 < eta /\ eta <= &1 / &4 /\
     x IN segment[vector[&0; -- &1 / &2; &0], vector[&0; --(&1 - eta); &0]:real^3]
     ==> x$1 = &0 /\ x$3 = &0 /\ x$2 < &0 /\ -- &1 < x$2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `u:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))))) THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_3] THEN
  MP_TAC(SPECL [`u:real`; `&1 / &2 - eta`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`&1 - u`; `&1 / &2 - eta`] REAL_LE_MUL) THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S3CL_SEG_AX_HI = prove
 (`!eta x.
     &0 < eta /\ eta <= &1 / &4 /\
     x IN segment[vector[&0; &1 - eta; &0], vector[&0; &1 / &2; &0]:real^3]
     ==> x$1 = &0 /\ x$3 = &0 /\ &0 < x$2 /\ x$2 < &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `u:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))))) THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_3] THEN
  MP_TAC(SPECL [`u:real`; `&1 / &2 - eta`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`&1 - u`; `&1 / &2 - eta`] REAL_LE_MUL) THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S3CL_SEG_FACE = prove
 (`!a b eta h x.
     a pow 2 + b pow 2 = &1 /\ &0 < eta /\ eta <= &1 / &4 /\
     (x IN segment[vector[&0; h; &0], vector[(&1 - eta) * a; h; (&1 - eta) * b]:real^3] \/
      x IN segment[vector[(&1 - eta) * a; h; (&1 - eta) * b], vector[&0; h; &0]:real^3])
     ==> x$2 = h /\ x$1 pow 2 + x$3 pow 2 < &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN (X_CHOOSE_THEN `u:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))))))) THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_3] THEN
  (CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]) THENL
   [MATCH_MP_TAC(REAL_ARITH `!p q. p = q /\ q < &1 ==> p < &1`) THEN
    EXISTS_TAC `(u * (&1 - eta)) pow 2` THEN CONJ_TAC THENL
     [UNDISCH_TAC `a pow 2 + b pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_1_LT THEN REWRITE_TAC[ARITH_EQ] THEN
    MP_TAC(SPECL [`u:real`; `&1 - eta`] REAL_LE_MUL) THEN
    MP_TAC(SPECL [`&1 - u`; `&1 - eta`] REAL_LE_MUL) THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `!p q. p = q /\ q < &1 ==> p < &1`) THEN
    EXISTS_TAC `((&1 - u) * (&1 - eta)) pow 2` THEN CONJ_TAC THENL
     [UNDISCH_TAC `a pow 2 + b pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_1_LT THEN REWRITE_TAC[ARITH_EQ] THEN
    MP_TAC(SPECL [`u:real`; `&1 - eta`] REAL_LE_MUL) THEN
    MP_TAC(SPECL [`&1 - u`; `&1 - eta`] REAL_LE_MUL) THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_S3CL_SEG_SIDE = prove
 (`!a b eta x.
     a pow 2 + b pow 2 = &1 /\ &0 < eta /\ eta <= &1 / &4 /\
     x IN segment[vector[(&1 - eta) * a; --(&1 - eta); (&1 - eta) * b],
                  vector[(&1 - eta) * a; &1 - eta; (&1 - eta) * b]:real^3]
     ==> x$1 = (&1 - eta) * a /\ x$3 = (&1 - eta) * b /\ abs(x$2) <= &1 - eta`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))))) THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_3] THEN
  MP_TAC(SPECL [`u:real`; `&1 - eta`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`&1 - u`; `&1 - eta`] REAL_LE_MUL) THEN
  ASM_REAL_ARITH_TAC);;

(* The polygonal path from qlo to qhi near the bottom face, the lateral     *)
(* segment through vector[a;0;b] and the top face: inside the model         *)
(* interior, each point either on the axis off 0 or within eta of S.        *)

let MOI_S3CL_RIM_PATH = prove
 (`!a b eta.
     a pow 2 + b pow 2 = &1 /\ &0 < eta /\ eta <= &1 / &4
     ==> ?c:real^3->bool.
           connected c /\ moi_s32_qlo IN c /\ moi_s32_qhi IN c /\
           !x. x IN c
               ==> x IN interior moi_s32_cyl /\
                   ((x IN moi_s32_axis /\ ~(x = vec 0)) \/
                    (?x'. x' IN {x:real^3 | x IN moi_s32_cyl /\
                                  (x$2 = -- &1 \/ x$2 = &1 \/ x$1 = a /\ x$3 = b)} /\
                          dist(x',x) <= eta))`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `segment[moi_s32_qlo, vector[&0; --(&1 - eta); &0]] UNION
              segment[vector[&0; --(&1 - eta); &0],
                      vector[(&1 - eta) * a; --(&1 - eta); (&1 - eta) * b]] UNION
              segment[vector[(&1 - eta) * a; --(&1 - eta); (&1 - eta) * b],
                      vector[(&1 - eta) * a; &1 - eta; (&1 - eta) * b]] UNION
              segment[vector[(&1 - eta) * a; &1 - eta; (&1 - eta) * b],
                      vector[&0; &1 - eta; &0]:real^3] UNION
              segment[vector[&0; &1 - eta; &0], moi_s32_qhi]` THEN
  REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC MOI_S3CL_CONN_SEG_UNION THEN CONJ_TAC THENL
      [ALL_TAC; REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT]]) THEN
    REWRITE_TAC[CONNECTED_SEGMENT];
    REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT];
    REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_S3GF_INTERIOR_CYL; IN_ELIM_THM; moi_s32_axis] THEN
  X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [(* the axis below *)
    MP_TAC(SPECL [`eta:real`; `x:real^3`] MOI_S3CL_SEG_AX_LO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM moi_s32_qlo]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      DISJ1_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `\z:real^3. z$2`) THEN
      REWRITE_TAC[VEC_COMPONENT] THEN ASM_REAL_ARITH_TAC];
    (* the bottom face *)
    MP_TAC(SPECL [`a:real`; `b:real`; `eta:real`; `--(&1 - eta)`; `x:real^3`]
      MOI_S3CL_SEG_FACE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `dist(vector[(x:real^3)$1; -- &1; x$3]:real^3,x) <= eta` ASSUME_TAC THENL
     [REWRITE_TAC[dist; NORM_LE_SQUARE; DOT_3; VECTOR_SUB_COMPONENT; VECTOR_3] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `!p. p = eta pow 2 ==> p <= eta pow 2`) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      DISJ2_TAC THEN EXISTS_TAC `vector[(x:real^3)$1; -- &1; x$3]:real^3` THEN
      ASM_REWRITE_TAC[moi_s32_cyl; IN_ELIM_THM; VECTOR_3] THEN ASM_REAL_ARITH_TAC];
    (* the lateral segment *)
    MP_TAC(SPECL [`a:real`; `b:real`; `eta:real`; `x:real^3`] MOI_S3CL_SEG_SIDE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `((&1 - eta) * a) pow 2 + ((&1 - eta) * b) pow 2 = (&1 - eta) pow 2`
    ASSUME_TAC THENL
     [UNDISCH_TAC `a pow 2 + b pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - eta) pow 2 < &1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_1_LT THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `dist(vector[a; (x:real^3)$2; b]:real^3,x) <= eta` ASSUME_TAC THENL
     [REWRITE_TAC[dist; NORM_LE_SQUARE; DOT_3; VECTOR_SUB_COMPONENT; VECTOR_3] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `!p. p = eta pow 2 ==> p <= eta pow 2`) THEN
      UNDISCH_TAC `a pow 2 + b pow 2 = &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      DISJ2_TAC THEN EXISTS_TAC `vector[a; (x:real^3)$2; b]:real^3` THEN
      ASM_REWRITE_TAC[moi_s32_cyl; IN_ELIM_THM; VECTOR_3] THEN ASM_REAL_ARITH_TAC];
    (* the top face *)
    MP_TAC(SPECL [`a:real`; `b:real`; `eta:real`; `&1 - eta`; `x:real^3`]
      MOI_S3CL_SEG_FACE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `dist(vector[(x:real^3)$1; &1; x$3]:real^3,x) <= eta` ASSUME_TAC THENL
     [REWRITE_TAC[dist; NORM_LE_SQUARE; DOT_3; VECTOR_SUB_COMPONENT; VECTOR_3] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `!p. p = eta pow 2 ==> p <= eta pow 2`) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      DISJ2_TAC THEN EXISTS_TAC `vector[(x:real^3)$1; &1; x$3]:real^3` THEN
      ASM_REWRITE_TAC[moi_s32_cyl; IN_ELIM_THM; VECTOR_3] THEN ASM_REAL_ARITH_TAC];
    (* the axis above *)
    MP_TAC(SPECL [`eta:real`; `x:real^3`] MOI_S3CL_SEG_AX_HI) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM moi_s32_qhi]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      DISJ1_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `\z:real^3. z$2`) THEN
      REWRITE_TAC[VEC_COMPONENT] THEN ASM_REAL_ARITH_TAC]]);;

(* The rim lies in the closure of W: otherwise the path of MOI_S3CL_RIM_PATH *)
(* with eta below the distance from S to the closure of W misses W, and its *)
(* g-image joins g qlo to g qhi in M minus the chain.                       *)

let MOI_S3CL_RIM_IN_CLOSURE = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> moi_s32_rim SUBSET
         closure {x | x IN moi_s32_cyl /\ g x IN moi_s32_chainset g hh bb}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SUBSET] THEN
  X_GEN_TAC `y0:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `?a b. a pow 2 + b pow 2 = &1 /\ y0 = vector[a; &0; b]:real^3`
  (X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real`
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THENL
   [MAP_EVERY EXISTS_TAC [`(y0:real^3)$1`; `(y0:real^3)$3`] THEN
    UNDISCH_TAC `(y0:real^3) IN moi_s32_rim` THEN
    REWRITE_TAC[moi_s32_rim; moi_s32_disk; IN_ELIM_THM; CART_EQ; DIMINDEX_3; FORALL_3;
                VECTOR_3] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S3CL_W_SUB) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s32_model] o CONJUNCT1) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gc") (CONJUNCTS_THEN2 (K ALL_TAC)
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`a:real`; `b:real`] MOI_S3CL_SHADOW) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sh")) THEN
  (* S misses the closure of W *)
  SUBGOAL_THEN
   `{x:real^3 | x IN moi_s32_cyl /\ (x$2 = -- &1 \/ x$2 = &1 \/ x$1 = a /\ x$3 = b)} INTER
    closure {x | x IN moi_s32_cyl /\ (g:real^3->real^3) x IN moi_s32_chainset g hh bb} = {}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    USE_THEN "sh" (MP_TAC o C MP (ASSUME `(x:real^3) IN {x:real^3 | x IN moi_s32_cyl /\
                    (x$2 = -- &1 \/ x$2 = &1 \/ x$1 = a /\ x$3 = b)}`) o SPEC `x:real^3`) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN moi_s32_cyl` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN {x:real^3 | x IN moi_s32_cyl /\
                    (x$2 = -- &1 \/ x$2 = &1 \/ x$1 = a /\ x$3 = b)}` THEN
      SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    ASM_CASES_TAC `(x:real^3) IN moi_s32_rim` THENL
     [SUBGOAL_THEN `x = vector[a; &0; b]:real^3` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
      MP_TAC(SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                    `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                    `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`;
                    `x:real^3`] MOI_S3CL_W_FRONTIER) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`{x:real^3 | x IN moi_s32_cyl /\ (x$2 = -- &1 \/ x$2 = &1 \/ x$1 = a /\ x$3 = b)}`;
    `closure {x | x IN moi_s32_cyl /\ (g:real^3->real^3) x IN moi_s32_chainset g hh bb}`]
    SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[CLOSED_CLOSURE] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d"))) THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `min (d / &2) (&1 / &4)`] MOI_S3CL_RIM_PATH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cp"))))) THEN
  (* the path misses W *)
  SUBGOAL_THEN `!x. x IN c ==> x IN interior moi_s32_cyl /\
                    ~((g:real^3->real^3) x IN moi_s32_chainset g hh bb)` (LABEL_TAC "cw")
  THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "cp" (MP_TAC o C MP (ASSUME `(x:real^3) IN c`) o SPEC `x:real^3`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[ASSUME `(x:real^3) IN interior moi_s32_cyl`] THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    SUBGOAL_THEN `(x:real^3) IN {x | x IN moi_s32_cyl /\
                    (g:real^3->real^3) x IN moi_s32_chainset g hh bb}` ASSUME_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN {x | x IN moi_s32_cyl /\
                    (g:real^3->real^3) x IN moi_s32_chainset g hh bb}` THEN
      UNDISCH_TAC `{x | x IN moi_s32_cyl /\
                    (g:real^3->real^3) x IN moi_s32_chainset g hh bb} SUBSET vec 0 INSERT v` THEN
      UNDISCH_TAC `DISJOINT (v:real^3->bool) moi_s32_axis` THEN
      UNDISCH_TAC `(x:real^3) IN moi_s32_axis` THEN UNDISCH_TAC `~(x:real^3 = vec 0)` THEN
      SET_TAC[];
      USE_THEN "d" (MP_TAC o SPECL [`x':real^3`; `x:real^3`]) THEN ANTS_TAC THENL
       [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MATCH_MP_TAC(SET_RULE `!s t x:real^3. x IN s /\ s SUBSET t ==> x IN t`) THEN
        EXISTS_TAC `{x | x IN moi_s32_cyl /\
                    (g:real^3->real^3) x IN moi_s32_chainset g hh bb}` THEN
        ASM_REWRITE_TAC[CLOSURE_SUBSET];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the image of the path contradicts the separation *)
  FIRST_ASSUM(MP_TAC o last o CONJUNCTS o GEN_REWRITE_RULE I [moi_s32_chain] o
              CONJUNCT2 o CONJUNCT2) THEN
  DISCH_TAC THEN MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] MOI_S3CL_SEP_CONN) THEN
  MAP_EVERY EXISTS_TAC [`moi_s32_open (g:real^3->real^3)`;
    `moi_s32_chainset (g:real^3->real^3) hh bb`; `{(g:real^3->real^3) moi_s32_qlo}`;
    `{(g:real^3->real^3) moi_s32_qhi}`; `IMAGE (g:real^3->real^3) c`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s32_cyl` THEN
    USE_THEN "gc" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "cw" (MP_TAC o C MP (ASSUME `(x:real^3) IN c`) o SPEC `x:real^3`) THEN
    MESON_TAC[INTERIOR_SUBSET; SUBSET];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_TAC THEN
    USE_THEN "cw" (MP_TAC o C MP (ASSUME `(x:real^3) IN c`) o SPEC `x:real^3`) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o CONJUNCT1 o MATCH_MP MOI_S3GF_MODEL_OPEN o CONJUNCT1) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_SING] THEN
    EXISTS_TAC `(g:real^3->real^3) moi_s32_qlo` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_SING] THEN
    EXISTS_TAC `(g:real^3->real^3) moi_s32_qhi` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S3CL_CLOSURE_EQ = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> closure (moi_s32_chainset g hh bb) =
         moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_S3CL_CLOSURE_SUB);
    REWRITE_TAC[UNION_SUBSET; CLOSURE_SUBSET] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
      [SYM(MATCH_MP MOI_S3CL_W_IMAGE th)]) THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`;
       `{x | x IN moi_s32_cyl /\ (g:real^3->real^3) x IN moi_s32_chainset g hh bb}`]
      MOI_S3CL_CLOSURE_IMAGE) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1); SET_TAC[]]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_S3CL_RIM_IN_CLOSURE)]);;


(* ------------------------------------------------------------------------- *)
(* Part 7. The theorem CELL.                                                 *)
(* ------------------------------------------------------------------------- *)

let CELL = prove
 (MOI_S32_CELL,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[pseudo_cell] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT2(CONJUNCT2(MATCH_MP MOI_S3GF_CHAIN_OPEN th))]) THEN
    REPEAT CONJ_TAC THENL
     [SET_TAC[];
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_S3CL_CHAINSET_DISK);
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_S3CL_GRIM_CIRCLE o CONJUNCT1);
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_S3CL_CLOSURE_EQ);
      REWRITE_TAC[moi_s32_chainset; IN_UNION; IN_SING];
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_S3CL_LOCALLY_POLY)];
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_S3GF_CHAIN_V)]);;

