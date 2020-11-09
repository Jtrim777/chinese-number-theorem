; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s

#|

This code serves as a algorithm for finding solutions to the Chinese Remainder Theorem.

The parameters are traditionally specified as a collection of 'a' values representing modular
congruencies, and a collection of corresponding 'n' values which represent the modulos over
which these values operate. 

This data is represented here as an association list of positive integers, where each 'a' value
is a key and the corresponding 'n' value is its val.
|#





; Find the GCD of two positive integers.
(definec gcd$ (x :pos y :pos) :pos
  (if (zp (mod x y))
    y
    (gcd$ y (mod x y))))

; A true list of positive integers
(defdata lop (oneof nil
                       (cons pos lop)))

; A pair of a congruence value and a moduli
(defdata anp (cons int pos))

; An association list mapping positive integers to positive integers
(defdata loanp (oneof (cons anp '()) (cons anp loanp)))

(definec rpp (x :pos y :pos) :bool
  (= 1 (gcd$ x y)))

; Is n relatively prime with all elements of l?
(definec rp-with-listp (n :pos l :lop) :bool
  (or (endp l)
      (and (rpp n (first l)) (rp-with-listp n (rest l)))))

(check= (rp-with-listp 3 (list 1 2 4 5 17)) t)
(check= (rp-with-listp 3 (list 1 2 4 18 5 17)) nil)

; Are all elements of l relatively prime with each other?
(definec all-rpp (l :lop) :bool
  (or (endp l)
      (and (rp-with-listp (car l) (cdr l)) (all-rpp (cdr l)))))

(check= (all-rpp (list 1 2 4 18 5 17)) nil)
(check= (all-rpp (list 1 2 5 17)) t)

; Get a list of the vals (aka not the keys) of an alist-pos.
(definec ex-mods (l :loanp) :lop
  (if (endp (rest l))
    `(,(cdr (first l)))
    (cons (cdr (first l)) (ex-mods (rest l)))))

; Are all the vals in this alist relatively prime?
; That is, are they valid mods for the CRT?
(definec good-modsp (l :loanp) :bool
  (all-rpp (ex-mods l)))

(check= (good-modsp (list (cons 3 5) (cons 4 7) (cons 25 8))) t)
(check= (good-modsp (list (cons 3 5) (cons 4 18) (cons 25 8))) nil)

; The product of all n values.
(definec product (l :lop) :nat
  (if (endp l)
    1
    (* (car l) (product (cdr l)))))

(check= (product '()) 1)
(check= (product '(3)) 3)
(check= (product '(3 1)) 3)
(check= (product '(3 5 7)) 105)
       

; Determines if x and y are congruent to each other mod m
(definec cong-mod (x :int y :int m :pos) :bool
  (equal (mod x m) (mod y m)))

(check= (cong-mod 3 3 5) t)
(check= (cong-mod 8 8 5) t)
(check= (cong-mod 3 8 5) t)
(check= (cong-mod 2 3 5) nil)

; Simplifies an a-n pair by moding the a by the n
(definec mod-anp (inp :anp) :anp
  (cons (mod (car inp) (cdr inp)) (cdr inp)))

(check= (mod-anp '(5 . 7)) '(5 . 7))
(check= (mod-anp '(12 . 7)) '(5 . 7))
(check= (mod-anp '(7 . 7)) '(0 . 7))

; Simplifies a loanp by calling mod-anp on all it's values
(definec mod-as (inp :loanp) :loanp
  (cond ((endp (rest inp)) `(,(mod-anp (first inp))))
        (t (cons (mod-anp (first inp))
                 (mod-as (rest inp))))))

(check= (mod-as '((19 . 5))) '((4 . 5)))
(check= (mod-as '((4 . 5))) '((4 . 5)))
(check= (mod-as '((19 . 5) (3 . 2))) '((4 . 5) (1 . 2)))

; Determines if ad is a valid ad value for these two pairs
(definec check-is-ad (lhs :anp rhs :anp ad :nat) :bool
  (cong-mod (car rhs) (+ (* ad (cdr lhs)) (car lhs)) (cdr rhs)))

; Finds a valid ad value starting from ad and working up to the cdr of the rhs
(definec find-ad-from (lhs :anp rhs :anp ad :nat) :nat
  :ic (rpp (cdr lhs) (cdr rhs))
  (cond ((check-is-ad lhs rhs ad) ad)
        ((> ad (cdr rhs)) 0)
        (t (find-ad-from lhs rhs (1+ ad)))))

; Finds a valid ad starting from zero
(definec find-ad (lhs :anp rhs :anp) :nat
  :ic (rpp (cdr lhs) (cdr rhs))
  (find-ad-from lhs rhs 0))

; Generates a d pair by finding a valid ad and joining it to the next modulo
(definec find-d (lhs :anp rhs :anp) :anp
  :ic (rpp (cdr lhs) (cdr rhs))
  (cons (find-ad lhs rhs) (cdr rhs)))

; Joins to a-n pairs by finding the pair where the a is congruent with the two input a's mod the
; two input n's, and the n is the product of the two input n's
(definec next-term (current :anp snd :anp) :anp
  :ic (rpp (cdr current) (cdr snd))
  (let ((d (find-d current snd)))
    (cons (+ (car current) (* (cdr current) (first d)))
          (* (cdr d) (cdr current)))))

(check= (next-term '(4 . 5) '(3 . 7)) '(24 . 35))

:program
; Collapses a list of moduli and congruence pairs into the pair that represents the solution and 
; the product of all the moduli.
; ACL2s is stupid and thinks the guards fail, despite us telling it not to bother
(definec fold-loanp (inp :loanp) :anp
  :ic (good-modsp inp)
  (declare (xargs :time-limit nil))
  (if (endp (cdr inp)) 
      (car inp)
      (next-term (car inp) (fold-loanp (cdr inp)))))

(check= (fold-loanp '((2 . 3) (19 . 5) (24 . 7))) '(59 . 105))
(check= (fold-loanp '((2 . 3) (4 . 5) (3 . 7))) '(59 . 105))
(check= (fold-loanp '((2 . 3))) '(2 . 3))
(check= (fold-loanp '((4 . 5) (3 . 7))) '(24 . 35))

; Finds a solution to the provided system of linear congruences
(definec solve-crt (inp :loanp) :int
  :ic (good-modsp inp)
  (let ((rez (fold-loanp inp)))
    (mod (car rez) (cdr rez))))

(check= (solve-crt '((2 . 3) (19 . 5) (24 . 7))) 59)
(check= (solve-crt '((2 . 3) (4 . 5) (3 . 7))) 59)
(check= (solve-crt '((2 . 3))) 2)
(check= (solve-crt '((4 . 5) (3 . 7))) 24)

; Determines if the given guess is a solution to the provided system of linear congruences
(definec is-solp (inp :loanp guess :int) :bool
  :ic (good-modsp inp)
  (if (endp (rest inp))
    (cong-mod guess (car (first inp)) (cdr (first inp)))
    (and (cong-mod guess (car (first inp)) (cdr (first inp)))
         (is-solp (rest inp) guess))))

(check= (is-solp '((2 . 3) (19 . 5) (24 . 7)) 59) t)
(check= (is-solp '((2 . 3) (4 . 5) (3 . 7)) 59) t)
(check= (is-solp '((2 . 3)) 2) t)
(check= (is-solp '((4 . 5) (3 . 7)) 24) t)
(check= (is-solp '((2 . 3) (19 . 5) (24 . 7)) 164) t)
(check= (is-solp '((2 . 3)) 5) t)
(check= (is-solp '((4 . 5) (3 . 7)) 59) t)
(check= (is-solp '((2 . 3) (19 . 5) (24 . 7)) 78) nil)
(check= (is-solp '((2 . 3)) 0) nil)
(check= (is-solp '((4 . 5) (3 . 7)) 15) nil)#|ACL2s-ToDo-Line|#

