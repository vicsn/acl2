; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lemmas for Signature::verify (sig-verify.lisp).
;
; Signature::verify (snarkVM circuit/account/src/signature/verify.rs), in
; synthesis order:
;   A::g_scalar_multiply(response)       net-gmul-gadget (to_bits_le of the
;                                        response, then the fixed-base fold)
;   pk_sig * challenge                   scalar-write-bits-le-gadget on the
;                                        challenge, grp-mul-gadget on the
;                                        reversed bits
;   g_nonce = gmul + mul                 Group::add with `this' = the mul
;                                        output (both operands variable)
;   hash_to_scalar_psd8(g_nonce.x, pk_sig.x, pr_sig.x, address.x, message)
;                                        hpos-c-hash-to-scalar, rate 8
;   compute_key.to_address()             key-c-ck-to-address, on the supply
;                                        after the hash's placeholder wire x
;                                        (x is substituted out of the hash
;                                        constraints and stays unallocated)
;   challenge.is_equal(candidate)        Field::is_not_equal on the challenge
;                                        wire and the 250-bit sum of the hash
;                                        bits (the constant top bit adds 0)
;   address.is_equal(candidate_address)  Group::is_equal
;   &                                    Boolean::and with `self' = 1 - r

(in-package "ALEOVM")

(include-book "key-ck-addr")
(include-book "key-h2s")
(include-book "enc-record-enc")
(include-book "rec-dynamic-record-eq")
(include-book "group-wire-sound")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (disable hpos-lc-eval-decomp)))

(set-ignore-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Boolean::and of the linear combination 1 - r and the wire g: (1 - r) (g) = (z).

(define sig-and-gadget ((r symbolp) (g symbolp) (z symbolp))
  :verify-guards nil
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 1) (list (1- (base-prime)) r))
         :b (list (list 1 g))
         :c (list (list 1 z)))))

(defruled sig-and-gadget-holds
  (implies (and (symbolp r) (symbolp g) (symbolp z)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg r)
                (r1cs::valuation-bindsp asg g)
                (r1cs::valuation-bindsp asg z))
           (equal (r1cs::r1cs-constraints-holdp (sig-and-gadget r g z) asg (base-prime))
                  (equal (pfield::mul (pfield::sub 1 (lookup-equal r asg) (base-prime))
                                      (lookup-equal g asg)
                                      (base-prime))
                         (lookup-equal z asg))))
  :use ((:instance prog-and-var-eq-gadget-to-mul (z g) (w z) (p (base-prime)))
        sig-and-gadget-is-prog)
  :in-theory '(primep-of-base-prime pfield::mul-commutative)
  :prep-lemmas
  ((defruled sig-and-gadget-is-prog
     (equal (r1cs::r1cs-constraints-holdp (sig-and-gadget r g z) asg (base-prime))
            (r1cs::r1cs-constraints-holdp (prog-and-var-eq-gadget g r z (base-prime))
                                          asg (base-prime)))
     :enable (sig-and-gadget prog-and-var-eq-gadget r1cs::r1cs-constraint-holdsp
              pfield::mul-commutative))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; pk_sig * challenge.

(define sig-mul-out (cbits ox oy steps)
  :verify-guards nil
  (b* ((out (grp-mul-out (rev cbits) ox oy steps)))
    (cons (first out) (second out))))

(defmacro sig-mul-hyps ()
  '(and (symbolp schal) (r1cs::valuation-bindsp asg schal)
        (symbol-listp cbits) (equal (len cbits) 251)
        (r1cs::valuation-binds-allp asg cbits)
        (symbol-listp crs) (equal (len crs) 250)
        (r1cs::valuation-binds-allp asg crs)
        (hpos-pt-boundp pk asg)
        (ecurve::edwards-bls12-pointp (hpos-pt-eval pk asg))
        (grp-steps-boundp steps asg)
        (equal (len steps) 250)
        (symbolp ox) (symbolp oy)
        (r1cs::valuation-bindsp asg ox) (r1cs::valuation-bindsp asg oy)
        (hpos-pt-boundp (sig-mul-out cbits ox oy steps) asg)
        (r1cs::r1cs-valuationp asg (base-prime))))

(defruled sig-mul-sound
  (implies (and (sig-mul-hyps)
                (r1cs::r1cs-constraints-holdp
                 (scalar-write-bits-le-gadget schal cbits crs (base-prime))
                 asg (base-prime))
                (r1cs::r1cs-constraints-holdp
                 (grp-mul-gadget (rev cbits) ox oy steps (car pk) (cdr pk) (base-prime))
                 asg (base-prime)))
           (b* ((c (lookup-equal schal asg)))
             (and (scalarp c)
                  (equal (lookup-equal-list cbits asg) (scalar-bits-le c))
                  (equal (hpos-pt-eval (sig-mul-out cbits ox oy steps) asg)
                         (group-mul-funspec (hpos-pt-eval pk asg) c)))))
  :do-not-induct t
  :use ((:instance scalar-write-bits-le-gadget-sound
                   (s schal) (xs cbits) (rs crs) (acc nil) (p (base-prime)))
        (:instance grp-mul-gadget-sound-funspec
                   (bits (rev cbits)) (bx (car pk)) (by (cdr pk))
                   (s (lookup-equal schal asg)) (p (base-prime)))
        (:instance enc-grp-bits-ok-when-bits (x cbits))
        (:instance enc-grp-bits-ok-of-rev (x cbits))
        (:instance acl2::consp-of-rev (x cbits))
        (:instance acl2::len-of-rev (x cbits)))
  :in-theory '(sig-mul-out hpos-pt-eval hpos-pt-boundp
               enc-grp-bit-vals-is-lookup-equal-list enc-lookup-equal-list-of-rev
               len car-cons cdr-cons (:e natp) (:e <) (:e len) (:e binary-+)
               (:e unary--) (:e bit-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The equalities and the conjunction.

(define sig-eq-gadget (schal bits ad ca m r mx rx my ry gout z)
  :verify-guards nil
  (append (rec-lc-neq-gadget (list (list 1 schal)) (pow2sum-vector bits 0) m r
                             (base-prime))
          (crv-group-is-equal-gadget (car ad) (cdr ad) (car ca) (cdr ca)
                                     mx rx my ry gout (base-prime))
          (sig-and-gadget r gout z)))

(defmacro sig-eq-hyps ()
  '(and (r1cs::r1cs-valuationp asg (base-prime))
        (symbolp schal) (r1cs::valuation-bindsp asg schal)
        (symbol-listp bits) (equal (len bits) 250)
        (r1cs::valuation-binds-allp asg bits)
        (bit-listp (lookup-equal-list bits asg))
        (hpos-pt-boundp ad asg) (hpos-pt-boundp ca asg)
        (ecurve::edwards-bls12-pointp (hpos-pt-eval ad asg))
        (ecurve::edwards-bls12-pointp (hpos-pt-eval ca asg))
        (symbolp m) (symbolp r) (symbolp mx) (symbolp rx) (symbolp my)
        (symbolp ry) (symbolp gout) (symbolp z)
        (r1cs::valuation-bindsp asg m) (r1cs::valuation-bindsp asg r)
        (r1cs::valuation-bindsp asg mx) (r1cs::valuation-bindsp asg rx)
        (r1cs::valuation-bindsp asg my) (r1cs::valuation-bindsp asg ry)
        (r1cs::valuation-bindsp asg gout) (r1cs::valuation-bindsp asg z)))

(defruled sig-bits-dot
  (implies (and (symbol-listp bits) (equal (len bits) 250)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg bits)
                (bit-listp (lookup-equal-list bits asg)))
           (equal (r1cs::dot-product (pow2sum-vector bits 0) asg (base-prime))
                  (lebits=>nat (lookup-equal-list bits asg))))
  :use ((:instance pow2sum-vector-to-mod-of-lebits=>nat
                   (xs bits) (i 0) (p (base-prime)))
        (:instance rec-lebits=>nat-bound (bs (lookup-equal-list bits asg))))
  :enable (primep-of-base-prime len-of-lookup-equal-list))

(defruled sig-eq-sound
  (implies (and (sig-eq-hyps)
                (r1cs::r1cs-constraints-holdp
                 (sig-eq-gadget schal bits ad ca m r mx rx my ry gout z)
                 asg (base-prime)))
           (equal (lookup-equal z asg)
                  (if (and (equal (lookup-equal schal asg)
                                  (lebits=>nat (lookup-equal-list bits asg)))
                           (equal (hpos-pt-eval ad asg) (hpos-pt-eval ca asg)))
                      1 0)))
  :do-not-induct t
  :use (sig-bits-dot
        (:instance rec-dot-of-var (m schal) (p (base-prime)))
        (:instance rec-lc-neq-gadget-bit
                   (va (list (list 1 schal))) (vb (pow2sum-vector bits 0)))
        (:instance crv-group-is-equal-wire-sound
                   (x1 (car ad)) (y1 (cdr ad)) (x2 (car ca)) (y2 (cdr ca))
                   (out gout) (p (base-prime))
                   (p1 (hpos-pt-eval ad asg)) (p2 (hpos-pt-eval ca asg)))
        (:instance sig-and-gadget-holds (g gout)))
  :in-theory (e/d (sig-eq-gadget r1cs::r1cs-constraints-holdp-of-append
                   hpos-pt-eval hpos-pt-boundp group-is-equal-funspec
                   primep-of-base-prime)
                  (rec-lc-neq-gadget crv-group-is-equal-gadget sig-and-gadget
                   pow2sum-vector)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The circuit.

(define sig-msg-lcs (msg)
  :verify-guards nil
  (if (endp msg)
      nil
    (cons (hpos-lc-var (car msg)) (sig-msg-lcs (cdr msg)))))

(define sig-xs (gx pkx prx adx msg)
  :verify-guards nil
  (list* (hpos-lc-var gx) (hpos-lc-var pkx) (hpos-lc-var prx) (hpos-lc-var adx)
         (sig-msg-lcs msg)))

(defund sig-c-verify (pk pr ad msg sr rb rrs rsts sc cb crs steps ox oy
                         sk kb krs ksts m r mx rx my ry gout z u vs asg)
  "Synthesis of Signature::verify: (mv out cs vs asg), out the output wire."
  (declare (xargs :verify-guards nil))
  (b* ((p (base-prime))
       (gcs (net-gmul-gadget sr rb rrs rsts p))
       (ccs (scalar-write-bits-le-gadget sc cb crs p))
       (mcs (grp-mul-gadget (rev cb) ox oy steps (car pk) (cdr pk) p))
       ((mv gn acs vs asg)
        (hpos-c-gadd (sig-mul-out cb ox oy steps) (key-gmul-wires rsts) vs asg))
       ((mv bits hcs vs asg)
        (hpos-c-hash-to-scalar 8 (sig-xs (car gn) (car pk) (car pr) (car ad) msg)
                               u vs asg))
       (vs (cdr vs))
       ((mv ca kcs vs asg) (key-c-ck-to-address pk pr sk kb krs ksts vs asg)))
    (mv z
        (append gcs ccs mcs acs hcs kcs
                (sig-eq-gadget sc bits ad ca m r mx rx my ry gout z))
        vs asg)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Stage 1: g_nonce.

(defruled sig-nonce-sound
  (implies (and (sig-mul-hyps)
                (net-gmul-hyps)
                (hpos-pt-boundp (key-gmul-wires sts) asg)
                (<= 6 (len vs))
                (symbol-listp (take 6 vs))
                (r1cs::valuation-binds-allp asg (take 6 vs))
                (r1cs::r1cs-constraints-holdp (net-gmul-gadget s rbits rs sts p) asg p)
                (r1cs::r1cs-constraints-holdp
                 (scalar-write-bits-le-gadget schal cbits crs (base-prime))
                 asg (base-prime))
                (r1cs::r1cs-constraints-holdp
                 (grp-mul-gadget (rev cbits) ox oy steps (car pk) (cdr pk) (base-prime))
                 asg (base-prime))
                (r1cs::r1cs-constraints-holdp
                 (hpos-gadd-cs (sig-mul-out cbits ox oy steps) (key-gmul-wires sts) vs)
                 asg (base-prime)))
           (b* ((c (lookup-equal schal asg))
                (e (lookup-equal s asg))
                (gn (hpos-pt-eval (cons (nth 4 vs) (nth 5 vs)) asg)))
             (and (scalarp c) (scalarp e)
                  (hpos-pt-boundp (cons (nth 4 vs) (nth 5 vs)) asg)
                  (ecurve::edwards-bls12-pointp gn)
                  (equal gn (group-add-funspec
                             (aleo-g-scalar-multiply-funspec e)
                             (group-mul-funspec (hpos-pt-eval pk asg) c))))))
  :do-not-induct t
  :use (sig-mul-sound key-gmul-wires-eval key-take-6-pt-boundp
        (:instance key-gadd-sound
                   (a (sig-mul-out cbits ox oy steps)) (b (key-gmul-wires sts)))
        (:instance hbhp-add-comm
                   (a (hpos-pt-eval (sig-mul-out cbits ox oy steps) asg))
                   (b (hpos-pt-eval (key-gmul-wires sts) asg)))
        (:instance edwards-bls12-pointp-of-aleo-g-scalar-multiply-funspec
                   (s (lookup-equal s asg)))
        (:instance edwards-bls12-pointp-of-group-mul-funspec
                   (p (hpos-pt-eval pk asg)) (s (lookup-equal schal asg)))
        (:instance ecurve::edwards-bls12-pointp-of-edwards-bls12-add
                   (ecurve::point1 (aleo-g-scalar-multiply-funspec (lookup-equal s asg)))
                   (ecurve::point2 (group-mul-funspec (hpos-pt-eval pk asg)
                                                      (lookup-equal schal asg)))))
  :in-theory '(hpos-gadd-sound-hyps group-add-funspec (:e base-prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Stage 2: the hash input evaluates to the preimage.

(defruled sig-fieldp-of-lookup
  (implies (and (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg v))
           (equal (mod (ifix (lookup-equal v asg)) (base-prime))
                  (lookup-equal v asg)))
  :use (:instance r1cs::fep-of-lookup-equal (var v) (valuation asg)
                  (prime (base-prime)))
  :enable pfield::fep)

(defruled key-eval-of-var
  (implies (and (symbolp v)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg v))
           (equal (hpos-lc-eval-list (list (hpos-lc-var v)) asg (base-prime))
                  (list (lookup-equal v asg))))
  :enable (hpos-lc-eval-list sig-fieldp-of-lookup))

(defruled sig-msg-lcs-eval
  (implies (and (symbol-listp msg)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg msg))
           (equal (hpos-lc-eval-list (sig-msg-lcs msg) asg (base-prime))
                  (lookup-equal-list msg asg)))
  :induct (len msg)
  :enable (sig-msg-lcs hpos-lc-eval-list lookup-equal-list
           r1cs::valuation-binds-allp key-eval-of-var))

(defruled sig-xs-eval
  (implies (and (symbolp gx) (symbolp pkx) (symbolp prx) (symbolp adx)
                (symbol-listp msg)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-bindsp asg gx) (r1cs::valuation-bindsp asg pkx)
                (r1cs::valuation-bindsp asg prx) (r1cs::valuation-bindsp asg adx)
                (r1cs::valuation-binds-allp asg msg))
           (equal (hpos-lc-eval-list (sig-xs gx pkx prx adx msg) asg (base-prime))
                  (list* (lookup-equal gx asg) (lookup-equal pkx asg)
                         (lookup-equal prx asg) (lookup-equal adx asg)
                         (lookup-equal-list msg asg))))
  :use sig-msg-lcs-eval
  :enable (sig-xs hpos-lc-eval-list key-eval-of-var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Composition.

(defruled key-ck-out
  (equal (mv-nth 0 (key-c-ck-to-address pk pr s rbits rs sts vs asg))
         (cons (nth 4 (nthcdr 6 vs)) (nth 5 (nthcdr 6 vs))))
  :enable (key-c-ck-to-address key-gadd-outs))

(defmacro sig-b* (b0 body)
  `(b* (,b0
(gn (cons (nth 4 vs) (nth 5 vs)))
    (asg1 (mv-nth 3 (hpos-c-gadd (sig-mul-out cb ox oy steps) (key-gmul-wires rsts)
                                 vs asg0)))
    (xs (sig-xs (nth 4 vs) (car pk) (car pr) (car ad) msg))
    ((mv bits hcs vs2h asg2) (hpos-c-hash-to-scalar 8 xs u (nthcdr 6 vs) asg1))
    (vs2 (cdr vs2h))
    ((mv & & vsp &) (hpos-c-poseidon-hash-many 8 xs 1 (nthcdr 6 vs) asg1))
    ((mv bs rs x &) (hpos-h2s-wires vsp))
    ((mv & kcs & &) (key-c-ck-to-address pk pr sk kb krs ksts vs2 asg2))
    (ca (cons (nth 4 (nthcdr 6 vs2)) (nth 5 (nthcdr 6 vs2)))))
     ,body))

(defruled sig-c-verify-split
  (sig-b* ((mv out cs & &) (sig-c-verify pk pr ad msg sr rb rrs rsts sc cb crs steps
                                      ox oy sk kb krs ksts m r mx rx my ry gout z
                                      u vs asg0))
    (and (equal out z)
         (equal cs (append (net-gmul-gadget sr rb rrs rsts (base-prime))
                           (scalar-write-bits-le-gadget sc cb crs (base-prime))
                           (grp-mul-gadget (rev cb) ox oy steps (car pk) (cdr pk)
                                           (base-prime))
                           (hpos-gadd-cs (sig-mul-out cb ox oy steps)
                                         (key-gmul-wires rsts) vs)
                           hcs kcs
                           (sig-eq-gadget sc bits ad ca m r mx rx my ry gout z)))))
  :enable (sig-c-verify key-gadd-outs key-ck-out))

(defruled sig-take-250-facts
  (implies (and (symbol-listp bs) (equal (len bs) 253)
                (r1cs::valuation-binds-allp asg bs)
                (bit-listp (lookup-equal-list bs asg)))
           (and (symbol-listp (take 250 bs))
                (equal (len (take 250 bs)) 250)
                (r1cs::valuation-binds-allp asg (take 250 bs))
                (equal (lookup-equal-list (take 250 bs) asg)
                       (take 250 (lookup-equal-list bs asg)))
                (bit-listp (take 250 (lookup-equal-list bs asg)))))
  :prep-books ((include-book "std/lists/take" :dir :system))
  :use ((:instance sig-take-lemmas (n 250)))
  :prep-lemmas
  ((defruled sig-take-lemmas
     (implies (and (natp n) (<= n (len bs)))
              (and (implies (symbol-listp bs) (symbol-listp (take n bs)))
                   (implies (r1cs::valuation-binds-allp asg bs)
                            (r1cs::valuation-binds-allp asg (take n bs)))
                   (equal (lookup-equal-list (take n bs) asg)
                          (take n (lookup-equal-list bs asg)))
                   (implies (bit-listp (lookup-equal-list bs asg))
                            (bit-listp (take n (lookup-equal-list bs asg))))))
     :induct (take n bs)
     :enable (take lookup-equal-list r1cs::valuation-binds-allp))))

(defmacro sig-verify-hyps ()
  '(and (r1cs::r1cs-valuationp asg (base-prime))
        ;; g_scalar_multiply(response)
        (symbolp sr) (symbol-listp rb) (symbol-listp rrs)
        (equal (len rb) 251) (equal (len rrs) 250)
        (r1cs::valuation-bindsp asg sr) (r1cs::valuation-binds-allp asg rb)
        (r1cs::valuation-binds-allp asg rrs) (net-gsts-okp (cdr rb) rsts asg)
        (hpos-pt-boundp (key-gmul-wires rsts) asg)
        ;; pk_sig * challenge
        (symbolp sc) (r1cs::valuation-bindsp asg sc)
        (symbol-listp cb) (equal (len cb) 251) (r1cs::valuation-binds-allp asg cb)
        (symbol-listp crs) (equal (len crs) 250) (r1cs::valuation-binds-allp asg crs)
        (grp-steps-boundp steps asg) (equal (len steps) 250)
        (symbolp ox) (symbolp oy)
        (r1cs::valuation-bindsp asg ox) (r1cs::valuation-bindsp asg oy)
        (hpos-pt-boundp (sig-mul-out cb ox oy steps) asg)
        ;; Group::new on pk_sig, pr_sig and the address
        (hpos-pt-boundp pk asg) (hpos-pt-boundp pr asg) (hpos-pt-boundp ad asg)
        (ecurve::edwards-bls12-pointp (hpos-pt-eval pk asg))
        (ecurve::edwards-bls12-pointp (hpos-pt-eval pr asg))
        (ecurve::edwards-bls12-pointp (hpos-pt-eval ad asg))
        ;; the message fields
        (symbol-listp msg) (r1cs::valuation-binds-allp asg msg)
        ;; g_nonce
        (<= 6 (len vs)) (symbol-listp (take 6 vs))
        (r1cs::valuation-binds-allp asg (take 6 vs))
        ;; hash_to_scalar_psd8
        (let ((rate 8) (asgx asg) (cs hcs)) (key-h2s-hyps))
        ;; compute_key.to_address()
        (symbolp sk) (symbol-listp kb) (symbol-listp krs)
        (equal (len kb) 251) (equal (len krs) 250)
        (r1cs::valuation-bindsp asg sk) (r1cs::valuation-binds-allp asg kb)
        (r1cs::valuation-binds-allp asg krs) (net-gsts-okp (cdr kb) ksts asg)
        (hpos-pt-boundp (key-gmul-wires ksts) asg)
        (<= 12 (len vs2))
        (symbol-listp (take 6 vs2)) (r1cs::valuation-binds-allp asg (take 6 vs2))
        (symbol-listp (take 6 (nthcdr 6 vs2)))
        (r1cs::valuation-binds-allp asg (take 6 (nthcdr 6 vs2)))
        ;; the equalities
        (symbolp m) (symbolp r) (symbolp mx) (symbolp rx) (symbolp my)
        (symbolp ry) (symbolp gout) (symbolp z)
        (r1cs::valuation-bindsp asg m) (r1cs::valuation-bindsp asg r)
        (r1cs::valuation-bindsp asg mx) (r1cs::valuation-bindsp asg rx)
        (r1cs::valuation-bindsp asg my) (r1cs::valuation-bindsp asg ry)
        (r1cs::valuation-bindsp asg gout) (r1cs::valuation-bindsp asg z)))

