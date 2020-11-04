; Lemma 2 - sol for smaller
(implies (and (loanpp l)
              (good-modsp l)
              (is-solp l x)
              (not (endp (rest l))))
         (is-solp (rest l) x))

; Context:
C1: (loanpp l)
C2: (good-modsp l)
C3: (is-solp l x)
C4: (not (endp (rest l)))

; Derived Context:
D1: (consp l) {C1, def loanpp}
D2: (consp (rest l)) {C4, C1}

; Goal
(is-solp (rest l) x)

; Proof
t
= {C3}
(is-solp l x)
={Def is-solp, instantiate ((inp l) (guess x))}
(if (endp (rest l))
    (cong-mod x (car (first l)) (cdr (first l)))
    (and (cong-mod x (car (first l)) (cdr (first l)))
         (is-solp (rest l) x)))
= {C4}
(if nil
    (cong-mod x (car (first l)) (cdr (first l)))
    (and (cong-mod x (car (first l)) (cdr (first l)))
         (is-solp (rest l) x)))
= {if axioms}
(and (cong-mod x (car (first l)) (cdr (first l)))
         (is-solp (rest l) x))
=> {boolean logic}
(is-solp (rest l) x)

; Lemma 3 - cong-mod-next-term
(implies (and (anpp x)
              (anpp y)
              (rpp (cdr x) (cdr y)))
         (cong-mod (mod (car (next-term x y)) (cdr (next-term x y)))
                   (car x) (cdr x)))

; Context:
C1: (anpp x)
C2: (anpp y)
C3: (rpp (cdr x) (cdr y))

; Goal:
(cong-mod (mod (car (next-term x y)) (cdr (next-term x y)))
          (car x) (cdr x))

; Proof:
(cong-mod (mod (car (next-term x y)) 
               (cdr (next-term x y)))
          (car x) 
          (cdr x))
= {Def next-term, instantiate ((current x) (second y))}
(cong-mod (mod (car (cons (+ (car x) (* (cdr x) (first (find-d x y))))
                          (* (cdr (find-d x y)) (cdr x)))) 
               (cdr (cons (+ (car x) (* (cdr x) (first (find-d x y))))
                          (* (cdr (find-d x y)) (cdr x)))))
          (car x) 
          (cdr x))
= {cons-car-cdr axioms}
(cong-mod (mod (+ (car x) (* (cdr x) (first (find-d x y))))
               (* (cdr (find-d x y)) (cdr x)))
          (car x) 
          (cdr x))
= {Def cong-mod, instantiate ((x (mod (+ (car x) (* (cdr x) (first (find-d x y))))
               (* (cdr (find-d x y)) (cdr x)))) (y (car x)) (m (cdr x)))}
(= (mod (mod (+ (car x) (* (cdr x) (first (find-d x y))))
               (* (cdr (find-d x y)) (cdr x)))
        (cdr x))
   (mod (car x) (cdr x)))
= {mod arith}
(= (mod (+ (car x) (* (cdr x) (first (find-d x y))))
        (cdr x))
   (mod (car x) (cdr x)))
= {mod arith}
(= (mod (car x) (cdr x))
   (mod (car x) (cdr x)))
=
t

QED


; Conjecture 1 - Validity:
(implies (and (loanpp l)
              (good-modsp l))
         (is-solp l (solve-crt l)))

; Conjecture 1a - Validity: Contract Case 1
(implies (and (not (loanpp l))
              (good-modsp l))
         (is-solp l (solve-crt l)))

; Contract Completion
(implies (and (not (loanpp l))
              (good-modsp l)
              (loanpp l))
         (is-solp l (solve-crt l)))

; Context:
C1: (not (loanpp l))
C2: (good-modsp l)
C3: (loanpp l)

; Derived Context
D1: nil

QED

; Conjecture 1b - Validity: Contract Case 2
(implies (and (loanpp l))
              (not (good-modsp l))
         (is-solp l (solve-crt l)))

; Contract Completion
(implies (and (not (good-modsp l))
              (good-modsp l)
              (loanpp l))
         (is-solp l (solve-crt l)))

; Context:
C1: (not (good-modsp l))
C2: (good-modsp l)
C3: (loanpp l)

; Derived Context
D1: nil

QED

; Conjecture 1c - Validity: Base case for solve-crt
(implies (and (loanpp l)
              (good-modsp l)
              (endp (rest l)))
         (is-solp l (solve-crt l)))

; Context:
C1: (loanpp l)
C2: (good-modsp l)
C3: (endp (rest l))

; Derived Context
D1: (consp l) {C1, def loanpp}

; Goal
(is-solp l (solve-crt l))

; Proof
(is-solp l (solve-crt l))
= {Def solve-crt, instantiate ((inp l)), let axioms}
(is-solp l (mod (car (fold-loanp l)) (cdr (fold-loanp l))))
= {Def fold-loanp, instantiate ((inp l))}
(is-solp l (mod (car (if (endp (cdr l)) 
              (car l)
              (next-term (car l) (fold-loanp (cdr l)))))
     (cdr (if (endp (cdr l)) 
              (car l)
              (next-term (car l) (fold-loanp (cdr l)))))))
= {C3}
(is-solp l (mod (car (if t
              (car l)
              (next-term (car l) (fold-loanp (cdr l)))))
     (cdr (if t
              (car l)
              (next-term (car l) (fold-loanp (cdr l)))))))
= {if axioms}
(is-solp l (mod (car (car l)) (cdr (car l))))
= {Def is-solp, instantiate ((inp l) (guess (mod (car (car l)) (cdr (car l)))))}
(if (endp (rest l))
    (cong-mod (mod (car (car l)) (cdr (car l))) (car (first l)) (cdr (first l)))
    (and (cong-mod (mod (car (car l)) (cdr (car l))) (car (first l)) (cdr (first l)))
         (is-solp (rest l) (mod (car (car l)) (cdr (car l))))))
= {C3}
(if t
    (cong-mod (mod (car (car l)) (cdr (car l))) (car (first l)) (cdr (first l)))
    (and (cong-mod (mod (car (car l)) (cdr (car l))) (car (first l)) (cdr (first l)))
         (is-solp (rest l) (mod (car (car l)) (cdr (car l))))))
= {if axioms}
(cong-mod (mod (car (car l)) (cdr (car l))) (car (car l)) (cdr (car l)))
= {Def cong-mod, instantiate ((x (mod (car (car l)) (cdr (car l)))) (y (car (car l))) (m (cdr (car l))))}
(= (mod (mod (car (car l)) (cdr (car l))) (cdr (car l)))
   (mod (car (car l)) (cdr (car l))))
= {mod arith}
(= (mod (car (car l)) (cdr (car l)))
   (mod (car (car l)) (cdr (car l))))
=
t

QED

; Conjecture 1d - Validity: Inductive Case
(implies (and (loanpp l)
              (good-modsp l)
              (not (endp (cdr l)))
              (is-solp (cdr l) (solve-crt l)))
         (is-solp l (solve-crt l)))

; Context:
C1: (loanpp l)
C2: (good-modsp l)
C3: (not (endp (cdr l)))
C4: (is-solp (cdr l) (solve-crt l))

; Derived Context:
D1: (consp (rest l)) {C3, C1}
D2: (consp l) {C1}

; Goal
(is-solp l (solve-crt l))

; Proof 2
(is-solp l (solve-crt l))
= {Def is-solp, instantiate ((inp l) (guess (solve-crt l)))}
(if (endp (rest l))
    (cong-mod (solve-crt l) (car (first l)) (cdr (first l)))
    (and (cong-mod (solve-crt l) (car (first l)) (cdr (first l)))
         (is-solp (rest l) (solve-crt l))))
= {C3}
(if nil
    (cong-mod (solve-crt l) (car (first l)) (cdr (first l)))
    (and (cong-mod (solve-crt l) (car (first l)) (cdr (first l)))
         (is-solp (rest l) (solve-crt l))))
= {if axioms}
(and (cong-mod (solve-crt l) (car (first l)) (cdr (first l)))
     (is-solp (rest l) (solve-crt l)))
= {C4}
(and (cong-mod (solve-crt l) (car (first l)) (cdr (first l)))
     t)
= {boolean logic}
(cong-mod (solve-crt l) (car (first l)) (cdr (first l)))
= {Def solve-crt, instantiate ((inp l))}
(cong-mod (mod (car (fold-loanp l)) (cdr (fold-loanp l)))
          (car (first l)) (cdr (first l)))
= {Def fold-loanp, instantiate ((inp l))}
(cong-mod (mod (car (if (endp (cdr l)) 
                        (car l)
                        (next-term (car l) (fold-loanp (cdr l)))))
               (cdr (if (endp (cdr l)) 
                        (car l)
                        (next-term (car l) (fold-loanp (cdr l))))))
          (car (first l)) (cdr (first l)))
= {C3}
(cong-mod (mod (car (if nil
                        (car l)
                        (next-term (car l) (fold-loanp (cdr l)))))
               (cdr (if nil
                        (car l)
                        (next-term (car l) (fold-loanp (cdr l))))))
          (car (first l)) (cdr (first l)))
= {if axioms, macro resolution}
(cong-mod (mod (car (next-term (car l) (fold-loanp (cdr l))))
               (cdr (next-term (car l) (fold-loanp (cdr l)))))
          (car (car l)) (cdr (car l)))
= {Lemma 3, instantiate ((x (car l)) (y (fold-loanp (cdr l))))}
t

QED



#| YAY!!!!!!!!! |#

; Lemma 4 - cdr-fold-product
(implies (and (loanpp l)
              (good-modsp l))
         (= (cdr (fold-loanp l)) (product (ex-mods l))))

; Lemma 4a - cdr-fold-product: Contract Case 1
(implies (and (not (loanpp l))
              (good-modsp l))
         (= (cdr (fold-loanp l)) (product (ex-mods l))))

; Contract Completion
(implies (and (not (loanpp l))
              (loanpp l)
              (good-modsp l))
         (= (cdr (fold-loanp l)) (product (ex-mods l))))

; Context:
C1: (not (loanpp l))
C2: (loanpp l)
C3: (good-modsp l)

; Derived Context:
D1: nil {C1, C2}

QED

; Lemma 4b - cdr-fold-product: Contract Case 2
(implies (and (loanpp l)
              (not (good-modsp l)))
         (= (cdr (fold-loanp l)) (product (ex-mods l))))

; Contract Completion
(implies (and (not (good-modsp l))
              (loanpp l)
              (good-modsp l))
         (= (cdr (fold-loanp l)) (product (ex-mods l))))

; Context:
C1: (not (good-modsp l))
C2: (loanpp l)
C3: (good-modsp l)

; Derived Context:
D1: nil {C1, C3}

QED

; Lemma 4c - cdr-fold-product: Base Case
(implies (and (loanpp l)
              (good-modsp l)
              (endp (rest l)))
         (= (cdr (fold-loanp l)) (product (ex-mods l))))

; Context:
C1: (loanpp l)
C2: (good-modsp l)
C3: (endp (rest l))

; Derived Context:
D1: (= (product (ex-mods l)) (cdr (car l))) {C3, Def product, Def ex-mods}

; Goal
(= (cdr (fold-loanp l)) (product (ex-mods l)))

; Proof
(cdr (fold-loanp l))
= {Def fold-loanp, instantiate ((inp l))}
(cdr (if (endp (cdr l)) 
         (car l)
         (next-term (car l) (fold-loanp (cdr l)))))
= {C3}
(cdr (if t
         (car l)
         (next-term (car l) (fold-loanp (cdr l)))))
= {if axioms}
(cdr (car l))
= {D1}
(product (ex-mods l))

QED

; Lemma 4d - cdr-fold-product: Inductive Case
(implies (and (loanpp l)
              (good-modsp l)
              (not (endp (rest l)))
              (= (cdr (fold-loanp (cdr l))) (product (ex-mods (cdr l)))))
         (= (cdr (fold-loanp l)) (product (ex-mods l))))

; Context:
C1: (loanpp l)
C2: (good-modsp l)
C3: (not (endp (rest l)))
C4: (= (cdr (fold-loanp (cdr l))) (product (ex-mods (cdr l))))

; Goal
(= (cdr (fold-loanp l)) (product (ex-mods l)))

; Proof
(cdr (fold-loanp l))
= {Def fold-loanp, instantiate ((inp l))}
(cdr (if (endp (cdr l)) 
         (car l)
         (next-term (car l) (fold-loanp (cdr l)))))
= {C3}
(cdr (fold-loanp l))
= {Def fold-loanp, instantiate ((inp l))}
(cdr (if nil
         (car l)
         (next-term (car l) (fold-loanp (cdr l)))))
= {if axioms}
(cdr (next-term (car l) (fold-loanp (cdr l))))
= {Def next-term, instantiate ((current (car l)) (second (fold-loanp (cdr l))))}
(cdr (cons (+ (car (car l)) (* (cdr (car l)) (first (find-d (car l) (fold-loanp (cdr l))))))
          (* (cdr (find-d (car l) (fold-loanp (cdr l)))) (cdr (car l)))))
= {cons-car-cdr axioms}
(* (cdr (find-d (car l) (fold-loanp (cdr l)))) (cdr (car l)))
= {Def find-d, instantiate ((lhs (car l)) (rhs (fold-loanp (cdr l))))}
(* (cdr (cons (find-ad (car l) (fold-loanp (cdr l))) (cdr (fold-loanp (cdr l))))) (cdr (car l)))
= {cons-car-cdr axioms}
(* (cdr (fold-loanp (cdr l))) (cdr (car l)))
= {C4}
(* (product (ex-mods (cdr l))) (cdr (car l)))
= {Def product, Def ex-mods}
(product (ex-mods l))

QED


; Lemma 5 - sol-lt-prod
(implies (and (loanpp l)
              (good-modsp l))
         (< (solve-crt l) (product (ex-mods l))))

; Context:
C1: (loanpp l)
C2: (good-modsp l)

; Goal:
(< (solve-crt l) (product (ex-mods l)))

; Proof:
(solve-crt l)
= {Def solve-crt, instantiate ((inp l))}
(mod (car (fold-loanp l)) (cdr (fold-loanp l)))
= {Lemma 4}
(mod (car (fold-loanp l)) (product (ex-mods l)))
< {mod arith}
(product (ex-mods l))

QED



; Conjecture 2 - Uniqueness
(implies (and (loanpp l)
              (good-modsp l)
              (natp x)
              (< x (product (ex-mods l)))
              (not (equal x (solve-crt l))))
         (not (is-solp l x)))

; Conjecture 2a - Uniqueness: Contract Case 1
(implies (and (not (loanpp l))
              (good-modsp l)
              (natp x)
              (< x (product (ex-mods l)))
              (not (equal x (solve-crt l))))
         (not (is-solp l x)))

; Contract Completion
(implies (and (not (loanpp l))
              (loanpp l)
              (good-modsp l)
              (natp x)
              (< x (product (ex-mods l)))
              (not (equal x (solve-crt l))))
         (not (is-solp l x)))

; Context:
C1: (not (loanpp l))
C2: (loanpp l)
C3: (good-modsp l)
C4: (natp x)
C5: (< x (product (ex-mods l)))
C6: (not (equal x (solve-crt l)))

; Derived Context:
D1: nil {C1, C2}

QED

; Conjecture 2b - Uniqueness: Contract Case 2
(implies (and (loanpp l)
              (not (good-modsp l))
              (natp x)
              (< x (product (ex-mods l)))
              (not (equal x (solve-crt l))))
         (not (is-solp l x)))

; Contract Completion
(implies (and (loanpp l)
              (not (good-modsp l))
              (good-modsp l)
              (natp x)
              (< x (product (ex-mods l)))
              (not (equal x (solve-crt l))))
         (not (is-solp l x)))

; Context:
C1: (loanpp l)
C2: (not (good-modsp l))
C3: (good-modsp l)
C4: (natp x)
C5: (< x (product (ex-mods l)))
C6: (not (equal x (solve-crt l)))

; Derived Context:
D1: nil {C2, C3}

QED

; Contexture 2c - Uniqueness: Base Case
(implies (and (loanpp l)
              (good-modsp l)
              (natp x)
              (< x (product (ex-mods l)))
              (not (equal x (solve-crt l)))
              (endp (rest l)))
         (not (is-solp l x)))

; Context:
C1: (loanpp l)
C2: (good-modsp l)
C3: (< x (product (ex-mods l)))
C4: (not (equal x (solve-crt l)))
C5: (endp (rest l))

; Derived Context:
D1: (consp l) {Def loanpp, C1}
D2: (= (product (ex-mods l)) (cdr (first l))) {Def product, C5, Def ex-mods}
D3: (< x (cdr (first l))) {C3, D2}
D4: (is-solp l (solve-crt l)) {Conjecture 1, C1, C2}
D5: (cong-mod (solve-crt l) (car (first l)) (cdr (first l))) {Def is-solp, D4}
D6: (= (mod (solve-crt l) (cdr (first l)))
       (mod (car (first l)) (cdr (first l)))) {Def cong-mod, instantiate ((x (solve-crt l))
                                                                          (y (car (first l)))
                                                                          (m (cdr (first l))))}
D7: (= (solve-crt l) (mod (car (first l)) (cdr (first l)))) {Lemma 5, D2, D6, mod arith}

; Goal:
(not (is-solp l x))

; Proof
(not (is-solp l x))
= {Def is-solp, instantiate ((inp l) (guess x))}
(not (if (endp (rest l))
         (cong-mod x (car (first l)) (cdr (first l)))
         (and (cong-mod x (car (first l)) (cdr (first l)))
              (is-solp (rest l) x))))
= {C5}
(not (if t
         (cong-mod x (car (first l)) (cdr (first l)))
         (and (cong-mod x (car (first l)) (cdr (first l)))
              (is-solp (rest l) x))))
= {if axioms}
(not (cong-mod x (car (first l)) (cdr (first l))))
= {Def cong-mod, instantiate ((x x) (y (car (first l))) (m (cdr (first l))))}
(not (= (mod x (cdr (first l))) (mod (car (first l)) (cdr (first l)))))
= {D3, mod arith}
(not (= x (mod (car (first l)) (cdr (first l)))))
= {D7}
(not (= x (solve-crt l)))
= {C4}
t

QED

; Contexture 2d - Uniqueness: Inductive Case
(implies (and (loanpp l)
              (good-modsp l)
              (natp x)
              (< x (product (ex-mods l)))
              (not (equal x (solve-crt l)))
              (not (endp (rest l)))
              (not (is-solp (rest l) x)))
         (not (is-solp l x)))

; Context:
C1: (loanpp l)
C2: (good-modsp l)
C3: (< x (product (ex-mods l)))
C4: (not (equal x (solve-crt l)))
C5: (not (endp (rest l)))
C6: (not (is-solp (rest l) x))

; Derived Context:
D1: (is-solp l (solve-crt l)) {Conjecture 1, C1, C2}
D2: (< (solve-crt l) (product (ex-mods l))) {Lemma 5}
D3: (cong-mod (solve-crt l) (car (first l)) (cdr (first l))) {Def is-solp, D4}

; Goal:
(not (is-solp l x))

; Proof:
(not (is-solp l x))
= {Def is-solp, instantiate ((inp l) (guess x))}
(not (if (endp (rest l))
         (cong-mod x (car (first l)) (cdr (first l)))
         (and (cong-mod x (car (first l)) (cdr (first l)))
              (is-solp (rest l) x))))
= {C5}
(not (if nil
         (cong-mod x (car (first l)) (cdr (first l)))
         (and (cong-mod x (car (first l)) (cdr (first l)))
              (is-solp (rest l) x))))
= {if axioms}
(not (and (cong-mod x (car (first l)) (cdr (first l)))
          (is-solp (rest l) x)))
= {boolean logic}
(or (not (cong-mod x (car (first l)) (cdr (first l))))
    (not (is-solp (rest l) x)))
= {C6}
(or (not (cong-mod x (car (first l)) (cdr (first l)))) t)
= {boolean logic}
t

QED
