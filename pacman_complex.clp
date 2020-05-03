;///////////////////////////
;Μάργαρης Αλέξανρος ΑΜ171157
;Φάτσιος Στέφανος ΑΜ171008
;///////////////////////////
(defglobal
   ?*priority* = 0 ; Αριθμός του Salience για το φάντασμα για να γίνεται εναλλάξ. Πρώτα Πακ-μαν και μετά Φάντασμα.
)
 
(deffacts static_facts ; Τα facts του προγράμματος.
	(cell_at 1 1 fruits 0)                                                        
	(cell_at 1 2 fruits 1)                                                                
	(cell_at 1 3 fruits 0)                                                                 
	(cell_at 1 4 fruits 2)
	  
	(cell_at 2 1 fruits 1)
	(cell_at 2 2 fruits 0)
	(cell_at 2 3 fruits 2)
	(cell_at 2 4 fruits 0)
	  
	(cell_at 3 1 fruits 0)
	(cell_at 3 2 fruits 0)
	(cell_at 3 3 fruits 1)
	(cell_at 3 4 fruits 0)
	  
	(cell_at 4 1 fruits 0)
	(cell_at 4 2 fruits 1)
	(cell_at 4 3 fruits 0)
	(cell_at 4 4 fruits 0)
)

(deffacts moving_facts ; Τα facts που μετακινούνται στον πίνακα.
	(pacman 1 is_in 4 2)
	(pacman 2 is_in 4 4)
	(ghost 3 3)
)

(defrule begin ; Αρχικοποίηση του προγράμματος.
	(declare (salience 20))
	(initial-fact)
	=>
	  (set-strategy random) ; Δήλωση στρατηγικής.
	  (set-salience-evaluation every-cycle) ; Έλεγχος Salience σε κάθε κύκλο.
)

(defrule reach_goal ; Η τελική κατάσταση που πρέπει να υπάρχει για να τερματίσει το πρόγραμμα.
	(declare (salience 10))
	(cell_at 1 1 fruits 0)
	(cell_at 1 2 fruits 0)
	(cell_at 1 3 fruits 0)
	(cell_at 1 4 fruits 0)
	  
	(cell_at 2 1 fruits 0)
	(cell_at 2 2 fruits 0)
	(cell_at 2 3 fruits 0)
	(cell_at 2 4 fruits 0)
	  
	(cell_at 3 1 fruits 0)
	(cell_at 3 2 fruits 0)
	(cell_at 3 3 fruits 0)
	(cell_at 3 4 fruits 0)
	  
	(cell_at 4 1 fruits 0)
	(cell_at 4 2 fruits 0)
	(cell_at 4 3 fruits 0)
	(cell_at 4 4 fruits 0)
	=>
	  (printout t "Pacman ate all the fruits."  crlf)
	  (halt) ; Τερματισμός προγράμματος.
)


(defrule no_more_pacmans ; Κοιτάμε για το αν ζουν τα Πακ-μαν.
	(declare (salience 20))
    (and 
	  (not (exists (pacman 1 is_in ?x ?y))) 
	  (not (exists (pacman 2 is_in ?x ?y)))
	)
	=>
	  (printout t "All the Pacmans are dead."  crlf) 
	  (halt) ; Τερματισμός προγράμματος.
)


;/////////////////
;Κινήσεις Πακ-μανς
;/////////////////

(defrule move_up
	(declare (salience 1))
	?z <- (pacman ?i is_in ?x ?y)	  
	(cell_at =(- ?x 1) ?y fruits ?f)
	=>
	  (retract ?z)
	  (assert (pacman ?i is_in (- ?x 1) ?y))
	  (bind ?*priority* 2)
)

(defrule move_down
	(declare (salience 1))
	?z <- (pacman ?i is_in ?x ?y)
	(cell_at =(+ ?x 1) ?y fruits ?f)
	=>
	  (retract ?z)
	  (assert (pacman ?i is_in (+ ?x 1) ?y)) 
	  (bind ?*priority* 2)
)

(defrule move_left
	(declare (salience 1))
	?z <- (pacman ?i is_in ?x ?y)
	(cell_at ?x =(- ?y 1) fruits ?f)
	=>
	  (retract ?z)
	  (assert (pacman ?i is_in ?x (- ?y 1)))
	  (bind ?*priority* 2)
)

(defrule move_right
	(declare (salience 1))
	?z <- (pacman ?i is_in ?x ?y)
	(cell_at ?x =(+ ?y 1) fruits ?f)
	=>
	  (retract ?z)
	  (assert (pacman ?i is_in ?x (+ ?y 1))) 
	  (bind ?*priority* 2)
)

(defrule eat_fruit
	(declare (salience 4))
	(pacman ?i is_in ?x ?y)
	?z <- (cell_at ?x ?y  fruits ?f&~0)
	=>
	  (retract ?z)
	  (assert (cell_at ?x ?y fruits (- ?f 1)))  
)

;////////////////////
;Κινήσεις Φαντάσματος
;////////////////////

(defrule move_up_ghost
	(declare (salience ?*priority*))
	?v <- (ghost ?x ?y)
	(cell_at =(- ?x 1) ?y fruits ?f)
	=>
	  (retract ?v)
	  (assert (ghost (- ?x 1) ?y))
	  (bind ?*priority* 0)
)

(defrule move_down_ghost
	(declare (salience ?*priority*))
	?v <- (ghost ?x ?y) 
	(cell_at =(+ ?x 1) ?y fruits ?f)
	=>
	  (retract ?v)
	  (assert (ghost (+ ?x 1) ?y))
	  (bind ?*priority* 0) 
)

(defrule move_left_ghost
	(declare (salience ?*priority*))
	?v <- (ghost ?x ?y)
	(cell_at ?x =(- ?y 1) fruits ?f)
	=>
	  (retract ?v)
	  (assert (ghost ?x (- ?y 1)))
	  (bind ?*priority* 0)
)

(defrule move_right_ghost
	(declare (salience ?*priority*))
	?v <- (ghost ?x ?y)
	(cell_at ?x =(+ ?y 1) fruits ?f)
	=>
	  (retract ?v)
	  (assert (ghost ?x (+ ?y 1))) 
	  (bind ?*priority* 0)
)

(defrule eat_pacman
	(declare (salience 5))
	(ghost ?x ?y)
	?v <- (pacman ?i is_in ?x ?y)
	=>
	  (retract ?v) 
)
;//////////////////////////////////////////////////