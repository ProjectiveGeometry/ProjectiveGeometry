(echo "starting Z3, working with pg(2,2) ...")

(echo "--- points and lines ---")

(declare-datatypes () ((Point A B C D E F G))) ; points 
(declare-datatypes () ((Line ABF BCD CAE ADG BEG CFG DEF))) ; lines 

(declare-const x Point)
(declare-const y Point)
(declare-const z Point)
(declare-const t Point)

(echo "- distinct x y z t")
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


(echo "a1-exists")
(assert (forall ((x Point)) (forall ((y Point)) (exists ((l Line)) (and (i x l) (i y l))))))
(check-sat)

(echo "uniqueness")
(assert (forall ((x Point)) (forall ((y Point)) (forall ((l Line)) (forall ((m Line)) (=> (i x l) (=> (i y l) (=> (i x m) (=> (i y m) (or (= x y) (= l m)))))))))))
(check-sat) 

(echo "a1_unique")
(assert (forall ((x Point)) (forall ((y Point)) (forall ((l1 Line)) (forall ((l2 Line)) (=> (not (= x y)) (=> (i x l1) (=> (i y l1) (=> (i x l2) (=> (i y l2) (= l1 l2)))))))))))
(check-sat)

(echo "a2_unique")
(assert (forall ((l1 Line)) (forall ((l2 Line)) (forall ((x Point)) (forall ((y Point)) (=> (not (= l1 l2)) (=> (i x l1) (=> (i x l2) (=> (i y l1) (=> (i y l2) (= x y)))))))))))
(check-sat)

(echo "a2_exist")
(assert (forall ((l1 Line)) (forall ((l2 Line)) (exists ((x Point)) (and (i x l1) (i x l2))))))
(check-sat)

(echo "a3: there exist four points with no three collinear")
(assert (exists ((x Point)) (exists ((y Point)) (exists ((z Point)) (exists ((t Point)) (forall ((l Line))
	(and (distinct x y z t) 
        (and (=> (and (i x l) (i y l)) (and (not (i z l)) (not (i t l))))
        (and (=> (and (i x l) (i z l)) (and (not (i y l)) (not (i t l))))
        (and (=> (and (i x l) (i t l)) (and (not (i z l)) (not (i y l))))
        (and (=> (and (i z l) (i y l)) (and (not (i x l)) (not (i t l))))
        (and (=> (and (i t l) (i y l)) (and (not (i z l)) (not (i x l))))
             (=> (and (i z l) (i t l)) (and (not (i y l)) (not (i x l))))))))))))))))
(check-sat)

(define-fun online ((x Point) (y Point) (z Point) (l Line)) Bool (and (i x l) (and (i y l) (i z l))))
; Definition collinear A B C :=  exists l, Incid A l /\ Incid B l /\ Incid C l.

; Desargues 
(echo "Desargues")

(define-fun desargues ((alpha Point) (beta Point) (gamma Point)) Bool
(or (online alpha beta gamma ABF)
(or (online alpha beta gamma BCD)
(or (online alpha beta gamma CAE)
(or (online alpha beta gamma ADG)
(or (online alpha beta gamma BEG)
(or (online alpha beta gamma CFG)
    (online alpha beta gamma DEF))))))))

(define-fun statement_desargues ((O Point) (P Point) (Q Point) (R Point) (P1 Point) (Q1 Point) (R1 Point) (alpha Point) (beta Point) (gamma Point) (lP Line) (lQ Line) (lR Line) (lPQ Line) (lPR Line) (lQR Line) (lP1Q1 Line) (lP1R1 Line) (lQ1R1 Line)) Bool
(=>
(and (online P Q gamma lPQ)
(and (online P1 Q1 gamma lP1Q1)
(and (online P R beta lPR) 
(and (online P1 R1 beta lP1R1)
(and (online Q R alpha lQR) 
(and (online Q1 R1 alpha lQ1R1)) 
(and (online O P P1 lP) 
(and (online O Q Q1 lQ) 
(and (online O R R1 lR)
(and (not (exists ((l Line)) (online O P Q l)))
(and (not (exists ((l Line)) (online O P R l)))
(and (not (exists ((l Line)) (online O Q R l)))
(and (not (exists ((l Line)) (online P Q R l)))
(and (not (exists ((l Line)) (online P1 Q1 R1 l)))
     (or (not (= P P1)) (or (not (= Q Q1)) (not (= R R1)))))))))))))))))
(desargues alpha beta gamma)))

(define-fun statement_lQ1R1 ((O Point) (P Point) (Q Point) (R Point) (P1 Point) (Q1 Point) (R1 Point) (alpha Point) (beta Point) (gamma Point) 
(lP Line) (lQ Line) (lR Line) (lPQ Line) (lPR Line) (lQR Line) (lP1Q1 Line) (lP1R1 Line)) Bool
(and (statement_desargues O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR lP1Q1 lP1R1 ABF)
(and (statement_desargues O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR lP1Q1 lP1R1 BCD)
(and (statement_desargues O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR lP1Q1 lP1R1 CAE)
(and (statement_desargues O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR lP1Q1 lP1R1 ADG)
(and (statement_desargues O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR lP1Q1 lP1R1 BEG)
(and (statement_desargues O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR lP1Q1 lP1R1 CFG)
     (statement_desargues O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR lP1Q1 lP1R1 DEF))))))))

(define-fun statement_lQ1R1_lP1R1 ((O Point) (P Point) (Q Point) (R Point) (P1 Point) (Q1 Point) (R1 Point) (alpha Point) (beta Point) (gamma Point) 
(lP Line) (lQ Line) (lR Line) (lPQ Line) (lPR Line) (lQR Line) (lP1Q1 Line)) Bool
(and (statement_lQ1R1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR lP1Q1 ABF)
(and (statement_lQ1R1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR lP1Q1 BCD)
(and (statement_lQ1R1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR lP1Q1 CAE)
(and (statement_lQ1R1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR lP1Q1 ADG)
(and (statement_lQ1R1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR lP1Q1 BEG)
(and (statement_lQ1R1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR lP1Q1 CFG)
     (statement_lQ1R1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR lP1Q1 DEF))))))))

(define-fun statement_lQ1R1_lP1R1_lP1Q1 ((O Point) (P Point) (Q Point) (R Point) (P1 Point) (Q1 Point) (R1 Point) (alpha Point) (beta Point) (gamma Point) 
(lP Line) (lQ Line) (lR Line) (lPQ Line) (lPR Line) (lQR Line)) Bool
(and (statement_lQ1R1_lP1R1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR ABF)
(and (statement_lQ1R1_lP1R1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR BCD)
(and (statement_lQ1R1_lP1R1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR CAE)
(and (statement_lQ1R1_lP1R1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR ADG)
(and (statement_lQ1R1_lP1R1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR BEG)
(and (statement_lQ1R1_lP1R1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR CFG)
     (statement_lQ1R1_lP1R1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR DEF))))))))

(define-fun statement_lQ1R1_lP1R1_lP1Q1_lQR ((O Point) (P Point) (Q Point) (R Point) (P1 Point) (Q1 Point) (R1 Point) (alpha Point) (beta Point) (gamma Point) 
(lP Line) (lQ Line) (lR Line) (lPQ Line) (lPR Line)) Bool
(and (statement_lQ1R1_lP1R1_lP1Q1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR ABF)
(and (statement_lQ1R1_lP1R1_lP1Q1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR BCD)
(and (statement_lQ1R1_lP1R1_lP1Q1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR CAE)
(and (statement_lQ1R1_lP1R1_lP1Q1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR ADG)
(and (statement_lQ1R1_lP1R1_lP1Q1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR BEG)
(and (statement_lQ1R1_lP1R1_lP1Q1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR CFG)
     (statement_lQ1R1_lP1R1_lP1Q1 O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR DEF))))))))

(define-fun statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR ((O Point) (P Point) (Q Point) (R Point) (P1 Point) (Q1 Point) (R1 Point) (alpha Point) (beta Point) (gamma Point) 
(lP Line) (lQ Line) (lR Line) (lPQ Line)) Bool
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ ABF)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ BCD)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ CAE)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ ADG)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ BEG)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ CFG)
     (statement_lQ1R1_lP1R1_lP1Q1_lQR O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ DEF))))))))

(define-fun statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ ((O Point) (P Point) (Q Point) (R Point) (P1 Point) (Q1 Point) (R1 Point) (alpha Point) (beta Point) (gamma Point) 
(lP Line) (lQ Line) (lR Line) ) Bool
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR ABF)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR BCD)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR CAE)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR ADG)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR BEG)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR CFG)
     (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR DEF))))))))

(define-fun statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR ((O Point) (P Point) (Q Point) (R Point) (P1 Point) (Q1 Point) (R1 Point) (alpha Point) (beta Point) (gamma Point) 
(lP Line) (lQ Line)  ) Bool
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ O P Q R P1 Q1 R1 alpha beta gamma lP lQ ABF)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ O P Q R P1 Q1 R1 alpha beta gamma lP lQ BCD)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ O P Q R P1 Q1 R1 alpha beta gamma lP lQ CAE)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ O P Q R P1 Q1 R1 alpha beta gamma lP lQ ADG)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ O P Q R P1 Q1 R1 alpha beta gamma lP lQ BEG)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ O P Q R P1 Q1 R1 alpha beta gamma lP lQ CFG)
     (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ O P Q R P1 Q1 R1 alpha beta gamma lP lQ DEF))))))))

(define-fun statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ ((O Point) (P Point) (Q Point) (R Point) (P1 Point) (Q1 Point) (R1 Point) (alpha Point) (beta Point) (gamma Point) 
(lP Line)  ) Bool
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR O P Q R P1 Q1 R1 alpha beta gamma lP ABF)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR O P Q R P1 Q1 R1 alpha beta gamma lP BCD)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR O P Q R P1 Q1 R1 alpha beta gamma lP CAE)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR O P Q R P1 Q1 R1 alpha beta gamma lP ADG)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR O P Q R P1 Q1 R1 alpha beta gamma lP BEG)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR O P Q R P1 Q1 R1 alpha beta gamma lP CFG)
     (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR O P Q R P1 Q1 R1 alpha beta gamma lP DEF))))))))

(define-fun statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP ((O Point) (P Point) (Q Point) (R Point) (P1 Point) (Q1 Point) (R1 Point) (alpha Point) (beta Point) (gamma Point) ) Bool
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ O P Q R P1 Q1 R1 alpha beta gamma ABF)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ O P Q R P1 Q1 R1 alpha beta gamma BCD)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ O P Q R P1 Q1 R1 alpha beta gamma CAE)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ O P Q R P1 Q1 R1 alpha beta gamma ADG)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ O P Q R P1 Q1 R1 alpha beta gamma BEG)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ O P Q R P1 Q1 R1 alpha beta gamma CFG)
     (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ O P Q R P1 Q1 R1 alpha beta gamma DEF))))))))

(define-fun statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma ((O Point) (P Point) (Q Point) (R Point) (P1 Point) (Q1 Point) (R1 Point) (alpha Point) (beta Point) ) Bool
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP O P Q R P1 Q1 R1 alpha beta A)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP O P Q R P1 Q1 R1 alpha beta B)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP O P Q R P1 Q1 R1 alpha beta C)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP O P Q R P1 Q1 R1 alpha beta D)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP O P Q R P1 Q1 R1 alpha beta E)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP O P Q R P1 Q1 R1 alpha beta F)
     (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP O P Q R P1 Q1 R1 alpha beta G))))))))

(define-fun statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta ((O Point) (P Point) (Q Point) (R Point) (P1 Point) (Q1 Point) (R1 Point) (alpha Point) ) Bool
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma O P Q R P1 Q1 R1 alpha A)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma O P Q R P1 Q1 R1 alpha B)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma O P Q R P1 Q1 R1 alpha C)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma O P Q R P1 Q1 R1 alpha D)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma O P Q R P1 Q1 R1 alpha E)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma O P Q R P1 Q1 R1 alpha F)
     (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma O P Q R P1 Q1 R1 alpha G))))))))

(define-fun statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha ((O Point) (P Point) (Q Point) (R Point) (P1 Point) (Q1 Point) (R1 Point)  ) Bool
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta O P Q R P1 Q1 R1 A)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta O P Q R P1 Q1 R1 B)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta O P Q R P1 Q1 R1 C)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta O P Q R P1 Q1 R1 D)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta O P Q R P1 Q1 R1 E)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta O P Q R P1 Q1 R1 F)
     (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta O P Q R P1 Q1 R1 G))))))))

(define-fun statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1 ((O Point) (P Point) (Q Point) (R Point) (P1 Point) (Q1 Point)   ) Bool
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha O P Q R P1 Q1 A)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha O P Q R P1 Q1 B)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha O P Q R P1 Q1 C)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha O P Q R P1 Q1 D)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha O P Q R P1 Q1 E)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha O P Q R P1 Q1 F)
     (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha O P Q R P1 Q1 G))))))))

(define-fun statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1 ((O Point) (P Point) (Q Point) (R Point) (P1 Point)    ) Bool
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1 O P Q R P1 A)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1 O P Q R P1 B)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1 O P Q R P1 C)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1 O P Q R P1 D)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1 O P Q R P1 E)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1 O P Q R P1 F)
     (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1 O P Q R P1 G))))))))

(define-fun statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1 ((O Point) (P Point) (Q Point) (R Point)    ) Bool
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1 O P Q R A)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1 O P Q R B)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1 O P Q R C)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1 O P Q R D)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1 O P Q R E)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1 O P Q R F)
     (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1 O P Q R G))))))))

(define-fun statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R ((O Point) (P Point) (Q Point)     ) Bool
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1 O P Q A)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1 O P Q B)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1 O P Q C)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1 O P Q D)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1 O P Q E)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1 O P Q F)
     (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1 O P Q G))))))))

(define-fun statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R_Q ((O Point) (P Point)     ) Bool
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R O P A)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R O P B)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R O P C)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R O P D)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R O P E)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R O P F)
     (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R O P G))))))))

(define-fun statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R_Q_P ((O Point)) Bool
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R_Q O A)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R_Q O B)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R_Q O C)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R_Q O D)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R_Q O E)
(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R_Q O F)
     (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R_Q O G))))))))

(assert (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R_Q_P A))
;(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R_Q_P A)
;(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R_Q_P B)
;(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R_Q_P C)
;(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R_Q_P D)
;(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R_Q_P E)
;(and (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R_Q_P F)
;     (statement_lQ1R1_lP1R1_lP1Q1_lQR_lPR_lPQ_lR_lQ_lP_gamma_beta_alpha_R1_Q1_P1_R_Q_P G))))))))



; (assert (forall ((O Point) (P Point) (Q Point) (R Point) (P1 Point) (Q1 Point) (R1 Point) (alpha Point) (beta Point) (gamma Point) 
; (lP Line) (lQ Line) (lR Line) (lPQ Line) (lPR Line) (lQR Line) (lP1Q1 Line) (lP1R1 Line) (lQ1R1 Line))
; (statement_desargues O P Q R P1 Q1 R1 alpha beta gamma lP lQ lR lPQ lPR lQR lP1Q1 lP1R1 lQ1R1)))

(check-sat)

; simplify the statement  ABF BCD CAE ADG BEG CFG DEF
; make it work with veriT
; go into Coq


;(get-model)
;(get-info :all-statistics)


(echo "--- the end ---")


