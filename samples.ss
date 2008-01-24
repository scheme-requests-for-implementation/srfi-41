; Copyright (C) 2007 by Philip L. Bewig of Saint Louis, Missouri, USA.  All rights
; reserved.  Permission is hereby granted, free of charge, to any person obtaining a copy of
; this software and associated documentation files (the "Software"), to deal in the Software
; without restriction, including without limitation the rights to use, copy, modify, merge,
; publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to
; whom the Software is furnished to do so, subject to the following conditions: The above
; copyright notice and this permission notice shall be included in all copies or substantial
; portions of the Software.  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
; FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
; HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF
; CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR
; THE USE OR OTHER DEALINGS IN THE SOFTWARE.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; utilities

(define (identity obj) obj)

(define (const obj) (lambda x obj))

(define (negate pred?) (lambda (x) (not (pred? x))))

(define (lsec proc . args) (lambda x (apply proc (append args x))))

(define (rsec proc . args) (lambda x (apply proc (reverse (append (reverse args) (reverse x))))))

(define (compose . fns)
  (let comp ((fns fns))
    (cond
      ((null? fns) 'error)
      ((null? (cdr fns)) (car fns))
      (else
        (lambda args
          (call-with-values
            (lambda ()
              (apply
                (comp (cdr fns))
                args))
            (car fns)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; examples

(define-stream (file->stream filename)
  (let ((p (open-input-file filename)))
    (stream-let loop ((c (read-char p)))
      (if (eof-object? c)
          (begin (close-input-port p)
                 stream-null)
          (stream-cons c
            (loop (read-char p)))))))

(define-stream (qsort lt? strm)
  (if (stream-null? strm)
      stream-null
      (let ((x (stream-car strm))
            (xs (stream-cdr strm)))
        (stream-append
          (qsort lt?
            (stream-filter
              (lambda (u) (lt? u x))
              xs))
          (stream x)
          (qsort lt?
            (stream-filter
              (lambda (u) (not (lt? u x)))
              xs))))))

(define-stream (interleave x yy)
  (stream-match yy
    (() (stream (stream x)))
    ((y . ys)
      (stream-append
        (stream (stream-cons x yy))
        (stream-map
          (lambda (z) (stream-cons y z))
          (interleave x ys))))))

(define-stream (perms xs)
  (if (stream-null? xs)
      (stream (stream))
      (stream-concat
        (stream-map
          (lsec interleave (stream-car xs))
          (perms (stream-cdr xs))))))

(define (stream-split n strm)
  (values (stream-take n strm)
          (stream-drop n strm)))

(define-stream (stream-unique eql? strm)
  (if (stream-null? strm)
      stream-null
      (stream-cons (stream-car strm)
        (stream-unique eql?
          (stream-drop-while
            (lambda (x)
              (eql? (stream-car strm) x))
            strm)))))

(define (stream-maximum lt? strm)
  (stream-fold
    (lambda (x y) (if (lt? x y) y x))
    (stream-car strm)
    (stream-cdr strm))) 

(define (stream-fold-one proc strm)
  (stream-fold proc
    (stream-car strm)
    (stream-cdr strm)))

(define (stream-minimum lt? strm)
  (stream-fold-one
    (lambda (x y) (if (lt? x y) x y))
    strm))

(define-stream (isort lt? strm)
    (define-stream (insert strm x)
      (stream-match strm
        (() (stream x))
        ((y . ys)
          (if (lt? y x)
              (stream-cons y (insert ys x))
              (stream-cons x strm)))))
    (stream-fold insert stream-null strm))

(define (display-file filename)
  (stream-for-each display
    (file->stream filename)))

(define-stream (stream-member eql? obj strm)
  (stream-let loop ((strm strm))
    (cond ((stream-null? strm) #f)
          ((eql? obj (stream-car strm)) strm)
          (else (loop (stream-cdr strm))))))

(define (sigma f m n)
  (st?eam-fold + 0
    (stream-map f (stream-range m (+ n 1)))))

(define-stream (stream-merge lt? . strms)
  (define-stream (merge xx yy)
    (stream-match xx (() yy) ((x . xs)
      (stream-match yy (() xx) ((y . ys)
        (if (lt? y x)
            (stream-cons y (merge xx ys))
            (stream-cons x (merge xs yy))))))))
  (stream-let loop ((strms strms))
    (cond ((null? strms) stream-null)
          ((null? (cdr strms)) (car strms))
          (else (merge (car strms)
                       (apply stream-merge lt?
                         (cdr strms)))))))

(define (fact n)
  (stream-ref
    (stream-scan * 1 (stream-from 1)))
    n)

(define-stream (msort lt? strm)
  (let* ((n (quotient (stream-length strm) 2))
         (ts (stream-take n strm))
         (ds (stream-drop n strm)))
    (if (zero? n)
        strm
        (stream-merge lt?
          (msort < ts) (msort < ds)))))

(define (stream-partition pred? strm)
  (stream-unfolds
    (lambda (s)
      (if (stream-null? s)
          (values s '() '())
          (let ((a (stream-car s))
                (d (stream-cdr s)))
            (if (pred? a)
                (values d (list a) #f)
                (values d #f (list a))))))
    strm)) 

(define-stream (stream-finds eql? obj strm)
  (stream-of (car x)
    (x in (stream-zip (stream-from 0) strm))
    (eql? obj (cadr x))))

(define (stream-find eql? obj strm)
  (stream-car
    (stream-append
      (stream-finds eql? obj strm)
      (stream #f))))

(define-stream (stream-remove pred? strm)
  (stream-filter (negate pred?) strm))

(define stream-sum (lsec stream-fold + 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; infinite streams

(define nats
  (stream-cons 0
    (stream-map add1 nats)))

(define fibs
  (stream-cons 1
    (stream-cons 1
      (stream-map +
        fibs
        (stream-cdr fibs)))))

(define hamming
  (stream-unique =
    (stream-cons 1
      (stream-merge <
        (stream-map (lsec * 2) hamming)
        (stream-merge <
          (stream-map (lsec * 3) hamming)
          (stream-map (lsec * 5) hamming))))))

(define power-table
  (stream-of
    (stream-of (expt m n)
      (m in (stream-from 1)))
      (n in (stream-from 2))))

(define primes (let ()
  (define-stream (next base mult strm)
    (let ((first (stream-car strm))
          (rest (stream-cdr strm)))
      (cond ((< first mult)
              (stream-cons first
                (next base mult rest)))
            ((< mult first)
              (next base (+ base mult) strm))
            (else (next base
                    (+ base mult) rest)))))
  (define-stream (sift base strm)
    (next base (+ base base) strm))
  (define-stream (sieve strm)
    (let ((first (stream-car strm))
          (rest (stream-cdr strm)))
      (stream-cons first
        (sieve (sift first rest)))))
  (sieve (stream-from 2))))


(define rats
  (stream-iterate
    (lambda (x)
      (let* ((n (floor x))
             (y (- x n)))
        (/ (- n -1 y))))
    1))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; backtracking via the stream of successes

(define (check? i j m n)
  (or (= j n)
      (= (+ i j) (+ m n))
      (= (- i j) (- m n))))

(define (stream-and strm)
  (let loop ((strm strm))
    (cond ((stream-null? strm) #t)
          ((not (stream-car strm)) #f)
          (else (loop (stream-cdr strm))))))

(define (safe? p n)
  (let* ((len (stream-length p))
         (m (+ len 1)))
    (stream-and
      (stream-of
        (not (check? (car ij) (cadr ij) m n))
          (ij in (stream-zip
                   (stream-range 1 m)
                   p))))))

(define (queens m)
  (if (zero? m)
      (stream (stream))
      (stream-of (stream-append p (stream n))
        (p in (queens (- m 1)))
        (n in (stream-range 1 9))
        (safe? p n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; generators and co-routines

(define-stream (flatten tree)
  (cond ((null? tree) stream-nu?l)
        ((pair? (car tree))
          (stream-append
            (flatten (car tree))
            (flatten (cdr tree))))
        (else (stream-cons
                (car tree)
                (flatten (cdr tree))))))

(define (same-fringe? eql? tree1 tree2)
  (let loop ((t1 (flatten tree1))
             (t2 (flatten tree2)))
    (cond ((and (stream-null? t1)
                (stream-null? t2)) #t)
          ((or  (stream-null? t1)
                (stream-null? t2)) #f)
          ((not (eql? (stream-car t1)
                      (stream-car t2))) #f)
          (else (loop (stream-cdr t1)
                      (stream-cdr t2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; a pipeline of procedures

; Gettysburg Address -- Abraham Lincoln -- November 19, 1863
(define getty (list->stream (string->list (string-append
"Four score and seven years ago our fathers brought forth\n"
"on this continent a new nation, conceived in Liberty, and\n"
"dedicated to the proposition that all men are created equal.\n" 
"\n"
"Now we are engaged in a great civil war, testing whether\n"
"that nation, or any nation, so conceived and so dedicated,\n"
"can long endure.  We are met on a great battlefield of that\n"
"war.  We have come to dedicate a portion of that field, as\n"
"a final resting place for those who here gave their lives\n"
"that that nation might live.  It is altogether fitting and\n"
"proper that we should do this.\n"
"\n"
"But, in a larger sense, we can not dedicate -? we can not\n"
"consecrate -? we can not hallow ?- this ground.  The brave\n"
"men, living and dead, who struggled here, have consecrated\n"
"it, far above our poor power to add or detract.  The world\n"
"will little note, nor long remember what we say here, but\n"
"it can never forget what they did here.  It is for us the\n"
"living, rather, to be dedicated here to the unfinished work\n"
"which they who fought here have thus far so nobly advanced.\n"
"It is rather for us to be here dedicated to the great task\n"
"remaining before us ?- that from these honored dead we take\n"
"increased devotion to that cause for which they gave the\n"
"last full measure of devotion ?- that we here highly resolve\n"
"that these dead shall not have died in vain ?- that this\n"
"nation, under God, shall have a new birth of freedom ?- and\n"
"that government of the people, by the people, for the people,\n"
"shall not perish from the earth.\n"))))

(define (stream-fold-right f base strm) 
  (if (stream-null? strm)
      base
      (f (stream-car strm)
         (stream-fold-right f base
           (stream-cdr strm)))))

(define (stream-fold-right-one f strm)
  (stream-match strm
  ((x) x)
  ((x . xs)
    (f x (stream-fold-right-one f xs)))))

(define (breakon a)
  (stream-lambda (x xss)
    (if (equal? a x)
        (stream-append (stream (stream)) xss)
        (stream-append
          (stream (stream-append
              (stream x) (stream-car xss)))
          (stream-cdr xss)))))

(define-stream (lines strm) 
  (stream-fold-right
    (breakon #\newline)
    (stream (stream))
    strm))

(define-stream (words strm)
  (stream-filter stream-pair?
    (stream-fold-right
      (breakon #\space)
      (stream (stream))
      strm)))

(define-stream (paras strm)
  (stream-filter stream-pair?
    (stream-fold-right
      (breakon stream-null)
      (stream (stream))
      strm)))

(define (insert a)
  (stream-lambda (xs ys)
    (stream-append xs (stream a) ys)))

(define unlines
  (lsec stream-fold-right-one
    (insert #\newline)))

(define unwords
  (lsec stream-fold-right-one
    (insert #\space)))

(define unparas
  (lsec stream-fold-right-one
    (insert stream-null)))

(define countlines
  (compose stream-length lines))

(define countwords
  (compose stream-length
           stream-concat
           (lsec stream-map words)
           lines))

(define countparas
  (compose stream-length paras lines))

(define parse
  (compose (lsec stream-map
             (lsec stream-map words))
           paras
           lines))

(define unparse
  (compose unlines
           unparas
           (lsec stream-map
             (lsec stream-map unwords))))

(define normalize (compose unparse parse))

(define (greedy m ws)
  (- (stream-length
       (stream-take-while (rsec <= m)
         (stream-scan
           (lambda (n word)
             (+ n (stream-length word) 1))
           -1
           ws))) 1))

(define-stream (fill m ws)
  (if (stream-null? ws)
      stream-null
      (let* ((n (greedy m ws))
             (fstline (stream-take n ws))
             (rstwrds (stream-drop n ws)))
        (stream-append
          (stream fstline)
          (fill m rstwrds)))))

(define linewords
  (compose stream-concat
           (lsec stream-map words)))

(define textparas
  (compose (lsec stream-map linewords)
           paras
           lines))

(define (filltext m strm)
  (unparse (stream-map (lsec fill m) (textparas strm))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; persistent queues

(define queue-null
  (cons stream-null stream-null))

(define (queue-null? x)
  (and (pair? x) (stream-null (car x))))

(define (queue-check f r)
  (if (< (stream-length r) (stream-length f))
      (cons f r)
      (cons (stream-append f (stream-reverse r))
            stream-null)))

(define (queue-snoc q x)
  (queue-check (car q) (stream-cons x (cdr q))))

(define (queue-head q)
  (if (stream-null? (car q))
      (error "empty queue: head")
      (stream-car (car q))))

(define (queue-tail q)
  (if (stream-null? (car q))
      (error "empty queue: tail")
      (queue-check (stream-cdr (car q))
                   (cdr q))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; reducing two passes to one

(define requests
  (stream
    '(get 3)
    '(put 1 "a")    ; use follows definition
    '(put 3 "c")    ; use precedes definition
    '(get 1)
    '(get 2)
    '(put 2 "b")    ; use precedes definition
    '(put 4 "d")))  ; unused definition

(define (get? obj) (eq? (car obj) 'get))

(define-stream (gets strm)
  (stream-map cadr (stream-filter get? strm)))

(define-stream (puts strm)
  (stream-map cdr  (stream-remove get? strm)))

(define-stream (run-dict requests)
  (let ((dict (build-dict (puts requests))))
    (stream-map (rsec stream-assoc dict)
      (gets requests))))

(define (stream-assoc key dict)
    (cond ((stream-null? dict) #f)
          ((equal? key (car (stream-car dict)))
            (stream-car dict))
          (else (stream-assoc key
                  (stream-cdr dict)))))

(define-stream (build-dict puts)
  (if (stream-null? puts)
      stream-null
      (stream-cons
        (stream-car puts)
        (build-dict (stream-cdr puts)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; pitfalls

(define (stream-equal? eql? xs ys)
  (cond ((and (stream-null? xs)
              (stream-null? ys)) #t)
        ((or (stream-null? xs)
             (stream-null? ys)) #f)
        ((not (eql? (stream-car xs)
                    (stream-car ys))) #f)
        (else (stream-equal? eql?
                (stream-cdr xs)
                (stream-cdr ys)))))