#lang racket
;; Write model programs as Coil, with the model's verdict on each, for
;; tests/diff.py to run the Coil checker over.
;;
;;   racket model/diff.rkt OUT-DIR N SEED
;;
;; writes OUT-DIR/cNNN.coil for the hand-written cases and OUT-DIR/pNNNNN.coil for
;; N random programs, and OUT-DIR/verdicts.txt: one line per program,
;;   NAME accept|reject|reborrow   a program written out (see `verdict`)
;;   NAME skipped REASON       a program Coil has no way to write
(require "rules.rkt" "cases.rkt" "search.rkt" "to-coil.rkt" racket/pretty)

;; `reborrow`: refused only because an exclusive reference is used after it was
;; moved. Coil never moves one: naming it lends what it refers to again, and the
;; checker holds that loan. The checker may accept such a program.
(define (verdict prog)
  (cond [(check-program prog) 'accept]
        [(parameterize ([mutant 'copy-mut]) (check-program prog)) 'reborrow]
        [else 'reject]))

(define (emit out-dir verdicts name prog)
  (define-values (text why) (program->coil prog (format "diff.~a" name)))
  ;; the model program too, to see why the model decided as it did
  (call-with-output-file (build-path out-dir (format "~a.model" name)) #:exists 'replace
    (λ (out) (pretty-write prog out)))
  (cond [text
         (call-with-output-file (build-path out-dir (format "~a.coil" name)) #:exists 'replace
           (λ (out) (write-string text out)))
         (fprintf verdicts "~a ~a\n" name (verdict prog))]
        [else (fprintf verdicts "~a skipped ~a\n" name why)]))

(module+ main
  (match (current-command-line-arguments)
    [(vector out-dir n seed)
     (make-directory* out-dir)
     (call-with-output-file (build-path out-dir "verdicts.txt") #:exists 'replace
       (λ (verdicts)
         (for ([c cases] [i (in-naturals)])
           (emit out-dir verdicts (format "c~a" (~r i #:min-width 3 #:pad-string "0")) (last c)))
         (random-seed (string->number seed))
         (for ([i (string->number n)])
           (emit out-dir verdicts (format "p~a" (~r i #:min-width 5 #:pad-string "0")) (gen-program)))))]))
