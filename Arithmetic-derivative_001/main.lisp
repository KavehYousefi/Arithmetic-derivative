;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;; This program implements routines for computing the arithmetic
;; derivative.
;; 
;; Concepts
;; ========
;; The arithmetic derivative constitutes a function defined on the
;; space of the natural numbers, including in this spectrum the zero
;; element, and associating with each member from this set another of
;; the same.
;; 
;; == DEFINITION ==
;; Two perspective may be assumed on the calculation of the arithmetic
;; derivative: a derivation from the Leipniz rule and a proceeding from
;; prime factorization.
;; 
;; Its first diorism proceeds by means of a quadruple postulation,
;; founded upon the Leibniz rule:
;;   
;;   (  i) 0' = 0
;;   ( ii) 1' = 0
;;   (iii) p' = 1, for any prime number p
;;   ( iv) (a * b)' = a' * b + a * b', for any a, b in N (Leibniz rule)
;; 
;; An alternative definition applies in reference to the principle of
;; prime factorization:
;;   
;;   n' = n * sum_{from i to r} (k[i] / p[i]),
;; 
;; where n is subjected to a prime factorization into its r tally of
;; distinct prime factors p[1] through p[r], each raised to a respective
;; exponent k[i] being a positive integer, that is:
;;   n = (p[1]^k[1]) * (p[2]^k[2]) * ... * (p[i]^k[i]) * ... * (p[r]^k[r])
;; 
;; 
;; Implementation
;; ==============
;; The warklooms of this implementation constitute a selection from the
;; most simple contemplations, the cambistry of which returns for this
;; investment a conspicuously inefficient produce, auspicious, however,
;; in a position as an epidictic vehicle.
;; 
;; == PRIME FACTORIZATION ==
;; The satisfaction of the chosen formula, based upon the principle of
;; prime factorization, proceeded, with all candor, in the manner of
;; andabatism: Incepting with the first member, the ordered series of
;; the prime numbers was traversed, testing for each element whether its
;; contribution manifested in the arithmetic derivative with an exponent
;; larger than zero, and gleaning such suitable candidates together with
;; their power in a list. Simultaneously, an accumulator's maintenance
;; appropriated any admitted prime-exponent pair k[i]/p[i], with k[i]
;; being the exponent to the prime p[i]. In its agency as a termination
;; condition, the gathering process would cease with the desinent
;; admittance that augmented the accumulator to a value equal to the
;; number n.
;; 
;; == PRIME FACTOR ACCUMULATION ==
;; The concluding step involves merely the eath application of the
;; priorly garnered prime-exponent quotients k[i]/p[i] into a summation.
;; The resulting sum, multiplied by the processed number n, already
;; defines the desiderated arithmetic derivative n'.
;; 
;; --------------------------------------------------------------------
;; 
;; Author: Kaveh Yousefi
;; Date:   2022-02-23
;; 
;; Sources:
;;   [mccallum2006exploration]
;;   -> "https://www.math.arizona.edu/~ura-reports/063/Sandhu.Aliana/Midterm.pdf"
;;       o Description and discussion of the arithmetic derivative.
;;   
;;   [number2012arithmeticderivative]
;;   -> "https://number.subwiki.org/wiki/Arithmetic_derivative"
;;       o Pellucid description and discussion of the arithmetic
;;         derivative.
;;   
;;   [oeiswiki2019arithmeticderivative]
;;   -> "http://oeis.org/wiki/Arithmetic_derivative"
;;       o Description of the arithmetic derivative.
;;   
;;   [rod2018factoringinalgebra]
;;   -> "https://www.mathsisfun.com/algebra/factoring.html"
;;       o Describes factorization.
;;   
;;   [rod2021fundtheoremofarithm]
;;   -> "https://www.mathsisfun.com/numbers/fundamental-theorem-arithmetic.html"
;;       o Describes the Fundamental Theorem of Arithmetic in simple
;;         terms.
;;       o The theorem states that:
;;           "Any integer greater than 1 is either a prime number, or
;;            can be written as a unique product of prime numbers
;;            (ignoring the order)."
;;   
;;   [rod2021primefactorization]
;;   -> "https://www.mathsisfun.com/prime-factorization.html"
;;       o Describes prime numbers and prime factorization in simple
;;         terms.
;;   
;;   [wikipedia2021arithmeticderivate]
;;   -> "https://en.wikipedia.org/wiki/Arithmetic_derivative"
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; -- Declaration of types.                                        -- ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftype list-of (&optional (element-type T))
  "The ``list-of'' type defines a list of zero or more elements, each
   of which conforms to the ELEMENT-TYPE, the same defaults to the
   comprehensive ``T''."
  (let ((predicate (gensym)))
    (declare (type symbol predicate))
    (setf (symbol-function predicate)
      #'(lambda (object)
          (declare (type T object))
          (and
            (listp object)
            (every
              #'(lambda (element)
                  (declare (type T element))
                  (typep element element-type))
              (the list object)))))
    `(satisfies ,predicate)))

;;; -------------------------------------------------------

(deftype prime-generator ()
  "The ``prime-generator'' type defines a niladic function which,
   starting with the value two (2), upon each invocation returns the
   next prime number."
  '(function () (integer 2 *)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; -- Prime number generator.                                      -- ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun prime-p (candidate)
  "Checks whether the CANDIDATE integer represents a prime number,
   returning on confirmation a ``boolean'' value of ``T'', otherwise
   ``NIL''."
  (declare (type (integer 2 *) candidate))
  (the boolean
    (loop
      for divisor
        of-type (integer 1 *)
        from    candidate
        downto  2
      when (zerop (mod candidate divisor))
        count 1 into number-of-divisors
      when (>= number-of-divisors 2)
        do (return NIL)
      finally
        (return T))))

;;; -------------------------------------------------------

(defun make-prime-generator ()
  "Creates and returns a niladic function which, starting with the value
   two (2), returns upon each invocation the next prime number.
   ---
   Example:
     ;; Print the first ten prime numbers to the standard output, that
     ;; is: 2, 3, 5, 7, 11, 13, 17, 19, 23, 29.
     (let ((generator (make-prime-generator)))
       (declare (type prime-generator generator))
       (loop repeat 10 do
         (print (funcall generator))))"
  (let ((next-prime 2))
    (declare (type (integer 2 *) next-prime))
    (the function
      #'(lambda ()
          (the (integer 2 *)
            (prog1 next-prime
              (loop
                do    (incf next-prime)
                until (prime-p next-prime))))))))

;;; -------------------------------------------------------

(defun get-next-prime (prime-generator)
  "Returns the next prime number from the PRIME-GENERATOR."
  (declare (type prime-generator))
  (the (integer 2 *) (funcall prime-generator)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; -- Implementation of adminicular functions.                     -- ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun get-exponent-for-prime (number prime)
  "Returns the exponent by which the PRIME number was raised in order
   to contribute to the product constructing the NUMBER.
   ---
   A concomitant of its arithmetic notion, the exponent represents the
   tally of occurrences of the PRIME in the NUMBER."
  (declare (type (integer 0 *) number))
  (declare (type (integer 2 *) prime))
  (the (integer 0 *)
    (loop
      with  remainder of-type (integer 0 *) = number
      while (zerop (mod remainder prime))
      do    (setf remainder (/ remainder prime))
      count 1)))

;;; -------------------------------------------------------

(defun get-prime-summands (number)
  "Returns for the NUMBER a list of those prime terms, each composed of
   a prime number p[i] divided into its exponent k[i] as the ratio
   k[i]/p[i], which by summation accumulate into the value of the
   NUMBER.
   ---
   As postulated by the fundamental theorem of arithmetic, any positive
   integer number can be represented as a product of one or more prime
   numbers {p[1], p[2], ..., p[r]}, with r being the tally of the
   constituent primes, contributing one or more times k[i], with k >= 1,
   in the form of an exponent to the prime, to the operation. In order
   to compute the arithmetic derivative, each prime number p[i] from
   {p[1], p[2], ..., p[r]} and its respective exponent k[i] from
   {k[1], k[2], ..., k[r]} are subjected to a division operation
   k[i]/p[i]. The members of this set {k[1]/p[1], k[1]/p[2], ...,
   k[1]/p[r]} are finally summed into the arithmetic derivative.
   ---
   This function, ``get-prime-summands'', returns the set {k[1]/p[1],
   k[1]/p[2], ..., k[1]/p[r]} as a list of ``rational''-typed elements.
   The desistence from solving the quotient's floating-point value
   conduces the obviation of rounding errors."
  (declare (type (integer 0 *) number))
  
  (let ((prime-generator (make-prime-generator)))
    (declare (type prime-generator))
    
    (the (list-of rational)
      (loop
        ;; The PRODUCT realizes the iteration's termination condition:
        ;; It is multiplied by all prime numbers contained in the NUMBER
        ;; a tally of times equal to their exponent. The moment the
        ;; PRODUCT equals the NUMBER, we can be ascertained that all
        ;; prime factors of the latter have been discovered, as the
        ;; PRODUCT has been constructed using the same.
        with product
          of-type (integer 1 *)
          =       1
        
        ;; As long as the PRODUCT does not equal the input NUMBER, not
        ;; all prime factors have been discovered yet.
        while (< product number)
        
        ;; Load the next prime number.
        for prime
          of-type (integer 2 *)
          =       (get-next-prime prime-generator)
        ;; Compute the exponent (tally) of the current PRIME in the
        ;; NUMBER.
        for prime-exponent
          of-type (integer 0 *)
          =       (get-exponent-for-prime number prime)
        
        ;; If the PRIME contributes to the NUMBER, that is, displays an
        ;; exponent (tally) greater than zero, collect the ratio
        ;;   k[i]
        ;;   ----
        ;;   p[i]
        ;; 
        ;; Update the PRODUCT to reflect the contribution of the current
        ;; PRIME by inducing it the tally PRIME-EXPONENT number of
        ;; times.
        when (plusp prime-exponent)
          collect (/ prime-exponent prime)
            into summands
          and do
            (setf product
              (* product
                 (expt prime prime-exponent)))
        
        finally
          (return summands)))))

;;; -------------------------------------------------------

(defun compute-arithmetic-derivative-using-prime-factorization (number)
  "Calculates and returns the arithmetic derivative of the NUMBER using
   prime factorization."
  (declare (type (integer 0 *) number))
  (the (integer 0 *)
    (* number
       (reduce #'+
         (get-prime-summands number)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; -- Implementation of public operations.                         -- ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun get-arithmetic-derivative (number)
  "Calculates and returns the arithmetic derivative of the NUMBER."
  (declare (type (integer 0 *) number))
  (the (integer 0 *)
    (cond
      ((zerop number)
        0)
      ((= number 1)
        0)
      ((prime-p number)
        1)
      (T
        (compute-arithmetic-derivative-using-prime-factorization
          number)))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; -- Test cases.                                                  -- ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns: 8.
(get-arithmetic-derivative 15)

;;; -------------------------------------------------------

;; Returns: 0.
(get-arithmetic-derivative 0)

;;; -------------------------------------------------------

;; Returns: 0.
(get-arithmetic-derivative 1)

;;; -------------------------------------------------------

;; Returns: 1.
(get-arithmetic-derivative 2)

;;; -------------------------------------------------------

;; Returns: 1.
(get-arithmetic-derivative 17)
