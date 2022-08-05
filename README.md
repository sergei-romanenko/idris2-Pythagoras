# Sqrt 2 is not rational

**Written by:** Ikegami Daisuke <ikegami.da@gmail.com>  
**Revised by:** Sergei Romanenko <sergei.romanenko@supercompilers.ru>

**The original proof** (in Agda1/Alfa) is due to Thierry Coquand.

This version tries to exploit the the Agda standard library.

## Links

* Idris: A Language for Type-Driven Development  
  <https://www.idris-lang.org/>
* The original proof on Agda1/Alfa  
  <http://www.cs.ru.nl/~freek/comparison/files/agda.alfa>
* The paper  
  <http://www.cs.ru.nl/~freek/comparison/comparison.pdf>
* Other proofs by another different proof assistants  
  <http://www.cs.ru.nl/~freek/comparison/>

## Files in `Coquand`

* `Cancellative.idr`  
  The definition of cancellative abelian monoid.

* `Theorem.idr`  
  The main theorem which is originally proved by Thierry Coquand:
  any prime cannot be a square of rational in cancellative
  abelian monoid.

---

* `2Divides.idr`  
  Some properties of natural numbers (with zero).

* `NatPlus.idr`  
  A set of natural numbers without zero.

---

* `Corollary.idr`  
  The set of the natural numbers without zero and  multiplication
  forms a cancellative abelian monoid.  
  Thus, the square root of two is irrational.

---

## Files in `Corbineau`

* `Sqrt2.idr`

  There is no m and n such that

    > `n ≢ 0` and `m * m ≡ 2 * (n * n)`

  Hence, sqrt 2 is irrational.

  The proof in Coq has been originally written by Pierre Corbineau  
  <http://www-verimag.imag.fr/~corbinea/ftp/programs/sqrt2.v>

---
