; CS 161 Spring 2013: HW3 skeleton

; FUNCTION: UNIFRAME
; PURPOSE:  Perform unification over the two inputs, based on the pseudocode
;           from Fig 9.1, p.328 of the textbook. Description also available
;           online at http://aima.cs.berkeley.edu/algorithms.pdf, page 23.
;           Each input is either a variable [(V var) list], frame, or list of
;           frames. As noted in the homework PDF and discussion #6, semantics
;           of frame unification are slightly different, so your code will not
;           match the pseudocode exactly. 
; OUTPUT:   A binding-list, of the form
;           (T (atom_1 binding_1) (atom_2 binding_2) ...),
;           where each atom_i is a *variable name* (as in, the second part of a
;           filler that looks like "(V name)") and each binding is a frame, 
;           (variable value) pair, or gap.
; INPUTS:   XX: variable (V var), frame, or list of frames
;           YY: variable (V var), frame, or list of frames
;           feta: a list of bindings, same format as output
;           (where (T) represents an initial empty binding list)

(setq VAR-PATHS nil)
(setq UNIXX nil)
(setq UNIYY nil)
(setq ERR 0)
(setq tfeta nil)
;(setq *gensym-counter* 0)

(defun f-pred (frame)
	(cond
		((listp frame) (first frame))
		(t frame)
	)
)

(defun f-length (frame)
	(cond
		((listp frame) (length frame))
		(t 1)
	)
)

(defun COMPARE-FRMS (frame1 frame2)
		(cond
		((null frame1) t)
		((not (equal (f-pred frame1) (f-pred frame2))) NIL)
		((<= (f-length frame1) 1) t)
		(t (let ((front (front-slot frame1))) 
					(and (COMPARE-FRMS (FILLER front frame1) (FILLER front frame2))
		           (COMPARE-FRMS (pop-slot frame1) (rm-slot front frame2)))
				)
		)
	)
)

(defun pop-slot (frame)
	(cons (first frame ) (nthcdr 2 frame))
)

(defun front-slot (frame)
	(first (second frame))
)

(defun front-filler (frame)
	(second (second frame))
)

(defun rm-slot (slot frame)
	(cond
		((<= (length frame) 1) frame)
		((equal (front-slot frame) slot) (pop-slot frame))
		(t (append (rm-slot slot (pop-slot frame)) (list (second frame))))
	)
)

(defun FILLER (slot frame)
	(cond
		((<= (length frame) 1) NIL)
		((equal slot (front-slot frame)) (front-filler frame))
		(t (FILLER slot (pop-slot frame)))
	)
)

(defun PATH-SL (slots concept)
	(cond
		((null slots) concept)
		(t (PATH-SL (rest slots) (FILLER (first slots) concept)))
	)
)

(defun GET-VAR (frame &optional (path nil))
	(cond
		((null (rest frame)) nil)
		((equal 'V (first (second (second frame))))
			(setq VAR-PATHS (append VAR-PATHS (list (append path (list (first (second frame)))))))
			(GET-VAR (cons (first frame) (rest (rest frame))) path))
		(t 
			(or
				(GET-VAR (second (second frame)) (append path (list (first (second frame)))))
				(GET-VAR (cons (first frame) (rest (rest frame))) path)
			)
		)
	)
)

(defun UNIPATH (XX YY feta paths)
	(cond
		((null paths) feta)
		(t
			(setf feta (append feta (list (UNIVAR (PATH-SL (first paths) XX) (PATH-SL (first paths) YY) feta))))
			(UNIPATH XX YY feta (rest paths))
		)
	)
)

(defun NILCHECKXX (feta)
	(cond
		((null (second feta)) nil)
		((equal (second (second feta)) nil) t)
		(t (NILCHECKXX (cons (first feta) (rest (rest feta)))))
	)
)

(defun NILCHECKYY (feta)
	(cond
		((null feta) nil)
		((equal (second (first feta)) nil) (NILCHECKYY (rest feta)))
		(t (cons (first feta) (NILCHECKYY (rest feta))))
	)
)

(defun CLEARGLOBS ()
	(setq VAR-PATHS nil)
	(setq UNIXX nil)
	(setq UNIYY nil)
)

(defun UNIFRAME (XX YY feta &optional (YYY YY))
	(cond
		((null feta) nil)
		((equal XX YY) feta)
		((and (equal (first XX) 'V) (equal (first YY) 'V)) feta) ; XX and YY are different variables
		((and (equal (first XX) 'V) (equal (length YY) 1)) (append feta (list (list (second XX) YY)))) ; XX is var, YY is pred
		((and (equal (first YY) 'V) (equal (length XX) 1)) (append feta (list (list (second YY) XX)))) ; YY is var, XX is pred
		((and (listp (first XX)) (atom (first YY))) nil) ; XX is a list of frames, YY is a single frame
		((and (listp (first XX)) (listp (first YY)) (> (length XX) (length YYY))) nil) ; XX has more frames than YY
		((and (listp (first XX)) (listp (first YY))) ; XX has equal or less frames than YY
			(cond
				((null YY) nil)
				((equal 1 (length XX)) (UNIFRAME (first XX) YY feta))
				((equal (f-pred (first XX)) (f-pred (first YY))) 
					(UNIFRAME (rest XX) YYY (UNIFRAME (first XX) (first YY) feta YYY))
					;(append (UNIFRAME (first XX) (first YY) feta YYY) (rest (UNIFRAME (rest XX) YYY feta YYY)))
				)
				(t (UNIFRAME XX (rest YY) feta YYY))
			)
		)
		((and (atom (first XX)) (atom (first YY))) ; XX is a frame, YY is a frame
			(setq VAR-PATHS nil)
			(GET-VAR XX)
			(setq UNIXX (UNIPATH XX YY feta VAR-PATHS))
			(cond
				((NILCHECKXX UNIXX) (CLEARGLOBS) nil)
				(t
					(setq VAR-PATHS nil)
					(GET-VAR YY)
					(setq UNIYY (UNIPATH YY XX UNIXX VAR-PATHS))
					(let ((temp (cons (first UNIYY) (NILCHECKYY (rest UNIYY)))))
						(CLEARGLOBS)
						(cond 
							((equal 1 ERR) (setq ERR 0) nil)
							((null (COMPARE-FRMS (SUBST-FETA XX temp) (SUBST-FETA YY temp))) nil)
							(t temp)
						)
					)
				)
			)
		)
		((and (atom (first XX)) (listp (first YY))) ; XX is a frame, YY is a list of frames
			(cond
				((null YY) nil)
				((equal (f-pred XX) (f-pred (first YY))) 
					(append (UNIFRAME XX (first YY) feta YYY)
					(rest (UNIFRAME XX (rest YY) feta YYY))))
				(t (UNIFRAME XX (rest YY) feta YYY))
			)
		)
		(t nil)
	)
)

; -----------------------------------------------------------------------------

; FUNCTION: UNIVAR
; PURPOSE:  Helper function for UNIFRAME. See pseudo-code from the textbook
;           algorithm UNIFY-VAR, from the same page as UNIFY referenced in
;           UNIFRAME. You should not implement or call OCCUR-CHECK?
; OUTPUT:   A binding-list (feta)
; INPUTS:   var: a variable (list formatted as (V var))
;           x: frame, variable, or frame list, as in UNIFRAME
;           feta: a binding list, same format as in UNIFRAME

(defun CONFLICT (var x feta)
	(cond
		((null (rest feta)) 0)
		((equal (second var) (first (first (rest feta))))
			(cond
				((equal x (second (first (rest feta)))) 1)
				(t 2)
			)
		)
		(t (CONFLICT var x (cons (first feta) (rest (rest feta)))))
	)
)

(defun UNIVAR (var x feta)
	(cond
		((equal 0 (CONFLICT var x feta)) (list (second var) x))
		((equal 1 (CONFLICT var x feta)) nil)
		((equal 2 (CONFLICT var x feta)) (setq ERR 1) nil)
	)
)

; -----------------------------------------------------------------------------

; FUNCTION: FFINFER
; PURPOSE:  Perform forward chaining, using a list of facts and rules (see INPUT).
;           Recursively build up a list of new facts derivable from this
;           knowledge base as NEW (see OUTPUT). See also FOL-FC-ASK from the text
;           (figure 9.3 on p332, online at http://aima.cs.berkeley.edu/algorithms.pdf, page 24)
;           although there are differences (see homework PDF)
; OUTPUT:   List of frames
; INPUTS:   FACTS: list of initial facts (list of instantiated frames, i.e.
;           frames containing no variables)
;           RULES: list of rules, with the following format:
;           ( (r_1-premise_1 r_1-premise_2 ... r_1-premise_n_1 ===> r_1-conclusion)
;             (r_2-premise_1 r_2-premise_2 ... r_2-premise_n_2 ===> r_2-conclusion)
;             ...
;           )
;           That is, for each rule, the second-to-last element is always a literal
;           "===>", signifying logical implication, the last element is the 
;           consequent of the implication, and the premises are the antecedants of
;           the implication (assumed to be conjoined). So eg:
;           ( (MONARCH (IS (V Q))) (FEMALE (IS (V Q))) ===> (ROYAL (IS (V Q))) ) is a
;           list of the single rule in first order logic
;           "forall Q (Monarch(Q) & Female(Q)) => Queen(Q)"
;           NEW: list of instantiated frames (containing no variables), to be
;           built up in recursive calls by applying premises to the current knowledge
;           base, and returned as output

(setq learned nil)

(defun KNOWN (new facts sfacts)
	(cond
		((null new) nil)
		((null facts) (cons (first new) (KNOWN (rest new) sfacts sfacts)))
		((equal (first new) (first facts)) (KNOWN (rest new) sfacts sfacts))
		(t (KNOWN new (rest facts) sfacts))
	)
)

(defun FFINFER (facts rules new)
	(setq lfacts facts)
	(loop for x in rules do
		(let 
			((temp (STANDARDIZE-VVARS x)))
			(print (reverse (rest (rest (reverse temp)))))
			(let ((conc (first (reverse temp)))
				(feta (UNIFRAME (reverse (rest (rest (reverse temp)))) facts '(T))))
				(cond
					((null feta) nil)
					((equal (SUBST-FETA conc feta) (SUBST-FETA conc (cons (first feta) (reverse (rest feta))))) (setf new (append new (list (SUBST-FETA conc feta)))))
					(t (setf new (append new (append (list (SUBST-FETA conc feta)) (list (SUBST-FETA conc (cons (first feta) (reverse (rest feta)))))))))
				)
			)
		)
	)
	(setf new (KNOWN new facts facts))
	(cond
		((null new) facts)
		(t 
			(setq learned (append new learned))
			(setf facts (append new facts))
			(FFINFER facts rules nil)
		)
	)
	learned
)

; -----------------------------------------------------------------------------

; FUNCTION: STANDARDIZE-VVARS
; PURPOSE:  Helper function for FFINFER. Takes a RULE formatted as in FFINFER
;           and replace all its variables with uniquely named ones. Eg,
;           (V X) should become (V X1234), or whatever the output of UNIQUE-GAP
;           happens to be).
; OUTPUT:   Rule with uniquely named variables
; INPUTS:   Rule to standardize, format is:
;           (premise-1 premise-2 ... premise-n ===> conclusion)

(setq *print-gensym* nil)

(defun UNIQUE-GAP (symName)
	(setq *gensym-counter* (1- *gensym-counter*))
	(intern (string (gensym (string symName))))
)

(defun STANDARDIZE-VVARS-HELPER2 (rule)
	(cond
		((listp (second rule))
			(cond
				((<= (length (second rule)) 1) rule)
				((>= (length (second rule)) 3) (list (first rule) (STANDARDIZE-VVARS-HELPER1 (second rule))))
				(t (list (first rule) (STANDARDIZE-VVARS-HELPER2 (second rule))))
			))
		(t (list (first rule) (UNIQUE-GAP (second rule))))
	)
)

(defun STANDARDIZE-VVARS-HELPER1 (rule)
	(cond
		((equal rule '===>) '===>)
		(t (cons (first rule) (mapcar #'STANDARDIZE-VVARS-HELPER2 (rest rule))))
	)
)

(defun STANDARDIZE-VVARS (rule &optional (inc 1))
	(cond
		((equal inc 1) (setq *gensym-counter* (1+ *gensym-counter*)))
	)
	(cond
		((null rule) nil)
		(t (cons (STANDARDIZE-VVARS-HELPER1 (first rule)) (STANDARDIZE-VVARS (rest rule) 0)))
	)
)

; -----------------------------------------------------------------------------

; FUNCTION: SUBST-FETAgs give
; PURPOSE:  Replace all variables in the given frame with their bindinn
;           in the binding-list feta.
; OUTPUT:   Instantiated frame, where variables have been replaced
; INPUTS:   frame: frame to replace variables in
;           feta: binding list, of the form from UNIFRAME
;           (T (var1 binding1) (var2 binding2) ...)

(defun FETCH-VAR (var feta)
	(cond
		((null (rest feta)) nil)
		((equal var (first (first (rest feta)))) (second (first (rest feta))))
		(t (FETCH-VAR var (cons (first feta) (rest (rest feta)))))
	)
)

(defun SUBST-FETA-HELPER (frame)
	(cond
		((listp (second frame))
			(cond
				((<= (length (second frame)) 1) frame)
				((>= (length (second frame)) 3) (list (first frame) (SUBST-FETA (second frame) tfeta)))
				(t (list (first frame) (SUBST-FETA-HELPER (second frame))))
			))
		(t (FETCH-VAR (second frame) tfeta))
	)
)

(defun SUBST-FETA (frame feta)
	(cond
		((null feta) nil)
	)
	(setq tfeta feta)
	(cons (first frame) (mapcar #'SUBST-FETA-HELPER (rest frame)))
)


(load "hw3-tests.txt")