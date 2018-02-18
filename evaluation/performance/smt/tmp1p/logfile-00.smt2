(get-info :version)
; (:version "4.5.1")
; Started: 2018-01-22 11:10:39
; Silicon.buildVersion: 1.1-SNAPSHOT 2102a44fa585+ default 2018/01/19 15:05:11
; Input file: null
; Verifier id: 00
; ------------------------------------------------------------
; Begin preamble
; ////////// Static preamble
; 
; ; /z3config.smt2
(set-option :print-success true) ; Boogie: false
(set-option :global-decls true) ; Boogie: default
(set-option :auto_config false) ; Usually a good idea
(set-option :smt.mbqi false)
(set-option :model.v2 true)
(set-option :smt.phase_selection 0)
(set-option :smt.restart_strategy 0)
(set-option :smt.restart_factor |1.5|)
(set-option :smt.arith.random_initial_value true)
(set-option :smt.case_split 3)
(set-option :smt.delay_units true)
(set-option :smt.delay_units_threshold 16)
(set-option :nnf.sk_hack true)
(set-option :smt.qi.eager_threshold 100)
(set-option :smt.qi.cost "(+ weight generation)")
(set-option :type_check true)
(set-option :smt.bv.reflect true)
; 
; ; /preamble.smt2
(declare-datatypes () ((
    $Snap ($Snap.unit)
    ($Snap.combine ($Snap.first $Snap) ($Snap.second $Snap)))))
(declare-sort $Ref 0)
(declare-const $Ref.null $Ref)
(define-sort $Perm () Real)
(define-const $Perm.Write $Perm 1.0)
(define-const $Perm.No $Perm 0.0)
(define-fun $Perm.isValidVar ((p $Perm)) Bool
	(<= $Perm.No p))
(define-fun $Perm.isReadVar ((p $Perm) (ub $Perm)) Bool
    (and ($Perm.isValidVar p)
         (not (= p $Perm.No))
         (< p $Perm.Write)))
(define-fun $Perm.min ((p1 $Perm) (p2 $Perm)) Real
    (ite (<= p1 p2) p1 p2))
(define-fun $Math.min ((a Int) (b Int)) Int
    (ite (<= a b) a b))
(define-fun $Math.clip ((a Int)) Int
    (ite (< a 0) 0 a))
; ////////// Sorts
(declare-sort ARPLog)
(declare-sort ARP_field_functions)
(declare-sort $FVF<$Ref>)
(declare-sort Set<$Snap>)
(declare-sort $PSF<$Snap>)
; ////////// Sort wrappers
; Declaring additional sort wrappers
(declare-fun $SortWrappers.IntTo$Snap (Int) $Snap)
(declare-fun $SortWrappers.$SnapToInt ($Snap) Int)
(assert (forall ((x Int)) (!
    (= x ($SortWrappers.$SnapToInt($SortWrappers.IntTo$Snap x)))
    :pattern (($SortWrappers.IntTo$Snap x))
    :qid |$Snap.Int|
    )))
(declare-fun $SortWrappers.BoolTo$Snap (Bool) $Snap)
(declare-fun $SortWrappers.$SnapToBool ($Snap) Bool)
(assert (forall ((x Bool)) (!
    (= x ($SortWrappers.$SnapToBool($SortWrappers.BoolTo$Snap x)))
    :pattern (($SortWrappers.BoolTo$Snap x))
    :qid |$Snap.Bool|
    )))
(declare-fun $SortWrappers.$RefTo$Snap ($Ref) $Snap)
(declare-fun $SortWrappers.$SnapTo$Ref ($Snap) $Ref)
(assert (forall ((x $Ref)) (!
    (= x ($SortWrappers.$SnapTo$Ref($SortWrappers.$RefTo$Snap x)))
    :pattern (($SortWrappers.$RefTo$Snap x))
    :qid |$Snap.$Ref|
    )))
(declare-fun $SortWrappers.$PermTo$Snap ($Perm) $Snap)
(declare-fun $SortWrappers.$SnapTo$Perm ($Snap) $Perm)
(assert (forall ((x $Perm)) (!
    (= x ($SortWrappers.$SnapTo$Perm($SortWrappers.$PermTo$Snap x)))
    :pattern (($SortWrappers.$PermTo$Snap x))
    :qid |$Snap.$Perm|
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.ARPLogTo$Snap (ARPLog) $Snap)
(declare-fun $SortWrappers.$SnapToARPLog ($Snap) ARPLog)
(assert (forall ((x ARPLog)) (!
    (= x ($SortWrappers.$SnapToARPLog($SortWrappers.ARPLogTo$Snap x)))
    :pattern (($SortWrappers.ARPLogTo$Snap x))
    :qid |$Snap.ARPLog|
    )))
(declare-fun $SortWrappers.ARP_field_functionsTo$Snap (ARP_field_functions) $Snap)
(declare-fun $SortWrappers.$SnapToARP_field_functions ($Snap) ARP_field_functions)
(assert (forall ((x ARP_field_functions)) (!
    (= x ($SortWrappers.$SnapToARP_field_functions($SortWrappers.ARP_field_functionsTo$Snap x)))
    :pattern (($SortWrappers.ARP_field_functionsTo$Snap x))
    :qid |$Snap.ARP_field_functions|
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.$FVF<$Ref>To$Snap ($FVF<$Ref>) $Snap)
(declare-fun $SortWrappers.$SnapTo$FVF<$Ref> ($Snap) $FVF<$Ref>)
(assert (forall ((x $FVF<$Ref>)) (!
    (= x ($SortWrappers.$SnapTo$FVF<$Ref>($SortWrappers.$FVF<$Ref>To$Snap x)))
    :pattern (($SortWrappers.$FVF<$Ref>To$Snap x))
    :qid |$Snap.$FVF<$Ref>|
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.Set<$Snap>To$Snap (Set<$Snap>) $Snap)
(declare-fun $SortWrappers.$SnapToSet<$Snap> ($Snap) Set<$Snap>)
(assert (forall ((x Set<$Snap>)) (!
    (= x ($SortWrappers.$SnapToSet<$Snap>($SortWrappers.Set<$Snap>To$Snap x)))
    :pattern (($SortWrappers.Set<$Snap>To$Snap x))
    :qid |$Snap.Set<$Snap>|
    )))
(declare-fun $SortWrappers.$PSF<$Snap>To$Snap ($PSF<$Snap>) $Snap)
(declare-fun $SortWrappers.$SnapTo$PSF<$Snap> ($Snap) $PSF<$Snap>)
(assert (forall ((x $PSF<$Snap>)) (!
    (= x ($SortWrappers.$SnapTo$PSF<$Snap>($SortWrappers.$PSF<$Snap>To$Snap x)))
    :pattern (($SortWrappers.$PSF<$Snap>To$Snap x))
    :qid |$Snap.$PSF<$Snap>|
    )))
; ////////// Symbols
(declare-fun ARPLog_sum ($Ref Int Int ARPLog) $Perm)
(declare-fun ARPLog_sum_gt ($Ref Int Int ARPLog) $Perm)
(declare-fun ARPLog_max_level (ARPLog) Int)
(declare-fun ARPLog_is_Cons (ARPLog) Bool)
(declare-fun ARPLog_is_Nil (ARPLog) Bool)
(declare-const ARPLog_type_Cons Int)
(declare-const ARPLog_type_Nil Int)
(declare-fun ARPLog_type (ARPLog) Int)
(declare-fun ARPLog_tail_Cons (ARPLog) ARPLog)
(declare-fun ARPLog_head_level_Cons (ARPLog) Int)
(declare-fun ARPLog_head_permission_Cons (ARPLog) $Perm)
(declare-fun ARPLog_head_fieldId_Cons (ARPLog) Int)
(declare-fun ARPLog_head_ref_Cons (ARPLog) $Ref)
(declare-fun ARPLog_Cons ($Ref Int $Perm Int ARPLog) ARPLog)
(declare-const ARPLog_Nil ARPLog)
(declare-const field_f Int)
; /dafny_axioms/qpp_sets_declarations_dafny.smt2 [Snap]
(declare-fun Set_equal (Set<$Snap> Set<$Snap>) Bool)
(declare-fun Set_in ($Snap Set<$Snap>) Bool)
(declare-fun Set_singleton ($Snap) Set<$Snap>)
; Declaring symbols related to program functions (from program analysis)
(declare-fun rdc ($Snap Int) $Perm)
(declare-fun rdc%limited ($Snap Int) $Perm)
(declare-fun rdc%stateless (Int) Bool)
(declare-fun epsilonRd ($Snap) $Perm)
(declare-fun epsilonRd%limited ($Snap) $Perm)
(declare-const epsilonRd%stateless Bool)
(declare-fun globalRd ($Snap) $Perm)
(declare-fun globalRd%limited ($Snap) $Perm)
(declare-const globalRd%stateless Bool)
(declare-fun rd ($Snap) $Perm)
(declare-fun rd%limited ($Snap) $Perm)
(declare-const rd%stateless Bool)
(declare-fun rdw ($Snap) $Perm)
(declare-fun rdw%limited ($Snap) $Perm)
(declare-const rdw%stateless Bool)
; Snapshot variable to be used during function verification
(declare-fun s@$ () $Snap)
; Declaring predicate trigger functions
; ////////// Uniqueness assumptions from domains
(assert (distinct field_f ARPLog_type_Nil ARPLog_type_Cons))
; ////////// Axioms
(assert (forall ((arp_quant_ref $Ref) (arp_quant_fieldId Int) (arp_quant_level Int) (arp_quant_log ARPLog)) (!
  (and
    (implies
      (ARPLog_is_Nil arp_quant_log)
      (=
        (ARPLog_sum arp_quant_ref arp_quant_fieldId arp_quant_level arp_quant_log)
        $Perm.No))
    (implies
      (ARPLog_is_Cons arp_quant_log)
      (=
        (ARPLog_sum arp_quant_ref arp_quant_fieldId arp_quant_level arp_quant_log)
        (+
          (ARPLog_sum arp_quant_ref arp_quant_fieldId arp_quant_level (ARPLog_tail_Cons arp_quant_log))
          (ite
            (and
              (= (ARPLog_head_ref_Cons arp_quant_log) arp_quant_ref)
              (and
                (= (ARPLog_head_fieldId_Cons arp_quant_log) arp_quant_fieldId)
                (= (ARPLog_head_level_Cons arp_quant_log) arp_quant_level)))
            (ARPLog_head_permission_Cons arp_quant_log)
            $Perm.No)))))
  :pattern ((ARPLog_sum arp_quant_ref arp_quant_fieldId arp_quant_level arp_quant_log))
  )))
(assert (forall ((arp_quant_ref $Ref) (arp_quant_fieldId Int) (arp_quant_level Int) (arp_quant_log ARPLog)) (!
  (and
    (implies
      (>= arp_quant_level (ARPLog_max_level arp_quant_log))
      (=
        (ARPLog_sum_gt arp_quant_ref arp_quant_fieldId arp_quant_level arp_quant_log)
        $Perm.No))
    (implies
      (< arp_quant_level (ARPLog_max_level arp_quant_log))
      (=
        (ARPLog_sum_gt arp_quant_ref arp_quant_fieldId arp_quant_level arp_quant_log)
        (+
          (ARPLog_sum_gt arp_quant_ref arp_quant_fieldId (+ arp_quant_level 1) arp_quant_log)
          (ARPLog_sum arp_quant_ref arp_quant_fieldId (+ arp_quant_level 1) arp_quant_log)))))
  :pattern ((ARPLog_sum_gt arp_quant_ref arp_quant_fieldId arp_quant_level arp_quant_log))
  )))
(assert (forall ((arp_quant_log ARPLog)) (!
  (= (ARPLog_max_level arp_quant_log) 6)
  :pattern ((ARPLog_max_level arp_quant_log))
  )))
(assert (and
  (forall ((arp_quant_log ARPLog)) (!
    (=
      (= (ARPLog_type arp_quant_log) (as ARPLog_type_Cons  Int))
      (ARPLog_is_Cons arp_quant_log))
    :pattern ((ARPLog_is_Cons arp_quant_log))
    ))
  (forall ((arp_quant_log ARPLog)) (!
    (=
      (= (ARPLog_type arp_quant_log) (as ARPLog_type_Cons  Int))
      (ARPLog_is_Cons arp_quant_log))
    :pattern ((ARPLog_type arp_quant_log))
    ))))
(assert (and
  (forall ((arp_quant_log ARPLog)) (!
    (=
      (= (ARPLog_type arp_quant_log) (as ARPLog_type_Nil  Int))
      (ARPLog_is_Nil arp_quant_log))
    :pattern ((ARPLog_is_Nil arp_quant_log))
    ))
  (forall ((arp_quant_log ARPLog)) (!
    (=
      (= (ARPLog_type arp_quant_log) (as ARPLog_type_Nil  Int))
      (ARPLog_is_Nil arp_quant_log))
    :pattern ((ARPLog_type arp_quant_log))
    ))))
(assert (and
  (forall ((arp_quant_log ARPLog)) (!
    (or
      (= (ARPLog_type arp_quant_log) (as ARPLog_type_Nil  Int))
      (= (ARPLog_type arp_quant_log) (as ARPLog_type_Cons  Int)))
    :pattern ((ARPLog_is_Nil arp_quant_log))
    ))
  (forall ((arp_quant_log ARPLog)) (!
    (or
      (= (ARPLog_type arp_quant_log) (as ARPLog_type_Nil  Int))
      (= (ARPLog_type arp_quant_log) (as ARPLog_type_Cons  Int)))
    :pattern ((ARPLog_is_Cons arp_quant_log))
    ))
  (forall ((arp_quant_log ARPLog)) (!
    (or
      (= (ARPLog_type arp_quant_log) (as ARPLog_type_Nil  Int))
      (= (ARPLog_type arp_quant_log) (as ARPLog_type_Cons  Int)))
    :pattern ((ARPLog_type arp_quant_log))
    ))))
(assert (forall ((arp_quant_head_ref $Ref) (arp_quant_head_fieldId Int) (arp_quant_head_permission $Perm) (arp_quant_head_level Int) (arp_quant_tail ARPLog)) (!
  (=
    (ARPLog_type (ARPLog_Cons arp_quant_head_ref arp_quant_head_fieldId arp_quant_head_permission arp_quant_head_level arp_quant_tail))
    (as ARPLog_type_Cons  Int))
  :pattern ((ARPLog_type (ARPLog_Cons arp_quant_head_ref arp_quant_head_fieldId arp_quant_head_permission arp_quant_head_level arp_quant_tail)))
  )))
(assert (= (ARPLog_type (as ARPLog_Nil  ARPLog)) (as ARPLog_type_Nil  Int)))
(assert (and
  (forall ((arp_quant_log ARPLog)) (!
    (implies
      (ARPLog_is_Cons arp_quant_log)
      (=
        arp_quant_log
        (ARPLog_Cons (ARPLog_head_ref_Cons arp_quant_log) (ARPLog_head_fieldId_Cons arp_quant_log) (ARPLog_head_permission_Cons arp_quant_log) (ARPLog_head_level_Cons arp_quant_log) (ARPLog_tail_Cons arp_quant_log))))
    :pattern ((ARPLog_head_ref_Cons arp_quant_log))
    ))
  (forall ((arp_quant_log ARPLog)) (!
    (implies
      (ARPLog_is_Cons arp_quant_log)
      (=
        arp_quant_log
        (ARPLog_Cons (ARPLog_head_ref_Cons arp_quant_log) (ARPLog_head_fieldId_Cons arp_quant_log) (ARPLog_head_permission_Cons arp_quant_log) (ARPLog_head_level_Cons arp_quant_log) (ARPLog_tail_Cons arp_quant_log))))
    :pattern ((ARPLog_head_fieldId_Cons arp_quant_log))
    ))
  (forall ((arp_quant_log ARPLog)) (!
    (implies
      (ARPLog_is_Cons arp_quant_log)
      (=
        arp_quant_log
        (ARPLog_Cons (ARPLog_head_ref_Cons arp_quant_log) (ARPLog_head_fieldId_Cons arp_quant_log) (ARPLog_head_permission_Cons arp_quant_log) (ARPLog_head_level_Cons arp_quant_log) (ARPLog_tail_Cons arp_quant_log))))
    :pattern ((ARPLog_head_permission_Cons arp_quant_log))
    ))
  (forall ((arp_quant_log ARPLog)) (!
    (implies
      (ARPLog_is_Cons arp_quant_log)
      (=
        arp_quant_log
        (ARPLog_Cons (ARPLog_head_ref_Cons arp_quant_log) (ARPLog_head_fieldId_Cons arp_quant_log) (ARPLog_head_permission_Cons arp_quant_log) (ARPLog_head_level_Cons arp_quant_log) (ARPLog_tail_Cons arp_quant_log))))
    :pattern ((ARPLog_head_level_Cons arp_quant_log))
    ))
  (forall ((arp_quant_log ARPLog)) (!
    (implies
      (ARPLog_is_Cons arp_quant_log)
      (=
        arp_quant_log
        (ARPLog_Cons (ARPLog_head_ref_Cons arp_quant_log) (ARPLog_head_fieldId_Cons arp_quant_log) (ARPLog_head_permission_Cons arp_quant_log) (ARPLog_head_level_Cons arp_quant_log) (ARPLog_tail_Cons arp_quant_log))))
    :pattern ((ARPLog_tail_Cons arp_quant_log))
    ))))
(assert (forall ((arp_quant_head_ref $Ref) (arp_quant_head_fieldId Int) (arp_quant_head_permission $Perm) (arp_quant_head_level Int) (arp_quant_tail ARPLog)) (!
  (and
    (=
      (ARPLog_head_ref_Cons (ARPLog_Cons arp_quant_head_ref arp_quant_head_fieldId arp_quant_head_permission arp_quant_head_level arp_quant_tail))
      arp_quant_head_ref)
    (and
      (=
        (ARPLog_head_fieldId_Cons (ARPLog_Cons arp_quant_head_ref arp_quant_head_fieldId arp_quant_head_permission arp_quant_head_level arp_quant_tail))
        arp_quant_head_fieldId)
      (and
        (=
          (ARPLog_head_permission_Cons (ARPLog_Cons arp_quant_head_ref arp_quant_head_fieldId arp_quant_head_permission arp_quant_head_level arp_quant_tail))
          arp_quant_head_permission)
        (and
          (=
            (ARPLog_head_level_Cons (ARPLog_Cons arp_quant_head_ref arp_quant_head_fieldId arp_quant_head_permission arp_quant_head_level arp_quant_tail))
            arp_quant_head_level)
          (=
            (ARPLog_tail_Cons (ARPLog_Cons arp_quant_head_ref arp_quant_head_fieldId arp_quant_head_permission arp_quant_head_level arp_quant_tail))
            arp_quant_tail)))))
  :pattern ((ARPLog_Cons arp_quant_head_ref arp_quant_head_fieldId arp_quant_head_permission arp_quant_head_level arp_quant_tail))
  )))
; End preamble
; ------------------------------------------------------------
; State saturation: after preamble
(set-option :timeout 100)
(check-sat)
; unknown
; ---------- FUNCTION rdc----------
(declare-fun count@0@00 () Int)
(declare-fun result@1@00 () $Perm)
; ----- Well-definedness of specifications -----
(push) ; 1
(assert (= s@$ $Snap.unit))
(assert false)
(pop) ; 1
(assert (forall ((s@$ $Snap) (count@0@00 Int)) (!
  (= (rdc%limited s@$ count@0@00) (rdc s@$ count@0@00))
  :pattern ((rdc s@$ count@0@00))
  )))
(assert (forall ((s@$ $Snap) (count@0@00 Int)) (!
  (rdc%stateless count@0@00)
  :pattern ((rdc%limited s@$ count@0@00))
  )))
; ---------- FUNCTION epsilonRd----------
(declare-fun result@2@00 () $Perm)
; ----- Well-definedness of specifications -----
(push) ; 1
(assert (= ($Snap.first s@$) $Snap.unit))
; [eval] none < result
(assert (< $Perm.No result@2@00))
(assert (= ($Snap.second s@$) $Snap.unit))
; [eval] result < write
(assert (< result@2@00 $Perm.Write))
(pop) ; 1
(assert (forall ((s@$ $Snap)) (!
  (= (epsilonRd%limited s@$) (epsilonRd s@$))
  :pattern ((epsilonRd s@$))
  )))
(assert (forall ((s@$ $Snap)) (!
  (as epsilonRd%stateless  Bool)
  :pattern ((epsilonRd%limited s@$))
  )))
(assert (forall ((s@$ $Snap)) (!
  (let ((result@2@00 (epsilonRd%limited s@$))) (and
    (< $Perm.No result@2@00)
    (< result@2@00 $Perm.Write)))
  :pattern ((epsilonRd%limited s@$))
  )))
; ---------- FUNCTION globalRd----------
(declare-fun result@3@00 () $Perm)
; ----- Well-definedness of specifications -----
(push) ; 1
(assert (= ($Snap.first s@$) $Snap.unit))
; [eval] none < result
(assert (< $Perm.No result@3@00))
(assert (= ($Snap.second s@$) $Snap.unit))
; [eval] result < write
(assert (< result@3@00 $Perm.Write))
(pop) ; 1
(assert (forall ((s@$ $Snap)) (!
  (= (globalRd%limited s@$) (globalRd s@$))
  :pattern ((globalRd s@$))
  )))
(assert (forall ((s@$ $Snap)) (!
  (as globalRd%stateless  Bool)
  :pattern ((globalRd%limited s@$))
  )))
(assert (forall ((s@$ $Snap)) (!
  (let ((result@3@00 (globalRd%limited s@$))) (and
    (< $Perm.No result@3@00)
    (< result@3@00 $Perm.Write)))
  :pattern ((globalRd%limited s@$))
  )))
; ---------- FUNCTION rd----------
(declare-fun result@4@00 () $Perm)
; ----- Well-definedness of specifications -----
(push) ; 1
(assert (= s@$ $Snap.unit))
(assert false)
(pop) ; 1
(assert (forall ((s@$ $Snap)) (!
  (= (rd%limited s@$) (rd s@$))
  :pattern ((rd s@$))
  )))
(assert (forall ((s@$ $Snap)) (!
  (as rd%stateless  Bool)
  :pattern ((rd%limited s@$))
  )))
; ---------- FUNCTION rdw----------
(declare-fun result@5@00 () $Perm)
; ----- Well-definedness of specifications -----
(push) ; 1
(assert (= s@$ $Snap.unit))
(assert false)
(pop) ; 1
(assert (forall ((s@$ $Snap)) (!
  (= (rdw%limited s@$) (rdw s@$))
  :pattern ((rdw s@$))
  )))
(assert (forall ((s@$ $Snap)) (!
  (as rdw%stateless  Bool)
  :pattern ((rdw%limited s@$))
  )))
