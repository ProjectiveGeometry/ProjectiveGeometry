(echo "starting Z3, working with pg(2,2) ...")

(echo "--- points and lines ---")

(declare-datatypes () ((Point A B C D E F G))) ; points 
(declare-datatypes () ((Line ABF BCD CAE ADG BEG CFG DEF))) ; lines 

(declare-const x Point)
(declare-const y Point)
(declare-const z Point)
(declare-const t Point)

(echo "--- distinct x y z t ---")
(assert (distinct x y z t))
(check-sat)

(echo "--- incidence relation ---")

(declare-fun i (Point Line) Bool)

; ABF
(assert (i A ABF))
(assert (i B ABF))
(assert (not (i C ABF)))
(assert (not (i D ABF)))
(assert (not (i E ABF)))
(assert (i F ABF))
(assert (not (i G ABF)))
; BCD
(assert (not (i A BCD)))
(assert (i B BCD))
(assert (i C BCD))
(assert (i D BCD))
(assert (not (i E BCD)))
(assert (not (i F BCD)))
(assert (not (i G BCD)))
; CAE
(assert (i A CAE))
(assert (not (i B CAE)))
(assert (i C CAE))
(assert (not (i D CAE)))
(assert (i E CAE))
(assert (not (i F CAE)))
(assert (not (i G CAE)))
; ADG
(assert (i A ADG))
(assert (not (i B ADG)))
(assert (not (i C ADG)))
(assert (i D ADG))
(assert (not (i E ADG)))
(assert (not (i F ADG)))
(assert (i G ADG))
; BEG
(assert (not (i A BEG)))
(assert (i B BEG))
(assert (not (i C BEG)))
(assert (not (i D BEG)))
(assert (i E BEG))
(assert (not (i F BEG)))
(assert (i G BEG))
; CFG
(assert (not (i A CFG)))
(assert (not (i B CFG)))
(assert (i C CFG))
(assert (not (i D CFG)))
(assert (not (i E CFG)))
(assert (i F CFG))
(assert (i G CFG))
; DEF
(assert (not (i A DEF)))
(assert (not (i B DEF)))
(assert (not (i C DEF)))
(assert (i D DEF))
(assert (i E DEF))
(assert (i F DEF))
(assert (not (i G DEF)))

(echo "--- basic tests ---")
(check-sat)
(define-fun a1 () Bool
(and (distinct x y z t) (and (i x ABF) (and (i y ABF) (i z ABF)))))
(assert a1)
(check-sat)

;(define-fun a1bis () Bool
;(and (distinct x y z t) (and (i x ABF) (and (i y ABF) (and (i z ABF) (and (i t ABF)))))))
;(assert a1bis)
;(check-sat)


(echo "--- a1-exists ---")
(assert (forall ((x Point)) (forall ((y Point)) (exists ((l Line)) (and (i x l) (i y l))))))
(check-sat)

(echo "--- uniqueness ---")
(assert (forall ((x Point)) (forall ((y Point)) (forall ((l Line)) (forall ((m Line)) (=> (i x l) (=> (i y l) (=> (i x m) (=> (i y m) (or (= x y) (= l m)))))))))))
(check-sat) 

(echo "--- a1_unique ---")
(assert (forall ((x Point)) (forall ((y Point)) (forall ((l1 Line)) (forall ((l2 Line)) (=> (not (= x y)) (=> (i x l1) (=> (i y l1) (=> (i x l2) (=> (i y l2) (= l1 l2)))))))))))
(check-sat)

(echo "--- a2_unique ---")
(assert (forall ((l1 Line)) (forall ((l2 Line)) (forall ((x Point)) (forall ((y Point)) (=> (not (= l1 l2)) (=> (i x l1) (=> (i x l2) (=> (i y l1) (=> (i y l2) (= x y)))))))))))
(check-sat)

(echo "--- a2_exist ---")
(assert (forall ((l1 Line)) (forall ((l2 Line)) (exists ((x Point)) (and (i x l1) (i x l2))))))
(check-sat)

(echo "--- a3: there exist four points with no three collinear ---")
(assert (exists ((x Point)) (exists ((y Point)) (exists ((z Point)) (exists ((t Point)) (forall ((l Line))
	(and (distinct x y z t) 
        (and (=> (and (i x l) (i y l)) (and (not (i z l)) (not (i t l))))
        (and (=> (and (i x l) (i z l)) (and (not (i y l)) (not (i t l))))
        (and (=> (and (i x l) (i t l)) (and (not (i z l)) (not (i y l))))
        (and (=> (and (i z l) (i y l)) (and (not (i x l)) (not (i t l))))
        (and (=> (and (i t l) (i y l)) (and (not (i z l)) (not (i x l))))
             (=> (and (i z l) (i t l)) (and (not (i y l)) (not (i x l))))))))))))))))
(check-sat)
(echo "--- OK: Fano plane is a projective plane ---")


(echo "--- the end ---")


